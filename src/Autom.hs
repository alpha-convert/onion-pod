{-# LANGUAGE  FlexibleContexts  #-}
module Autom where

import Events
import Types
import Stream
import qualified Data.Map as Map
import ElimTerm
import Control.Monad.State.Strict
import qualified Data.Bifunctor
import PrettyPrint
import Data.Maybe

type StateId = Int

data EventPat = EPIntEv | EPCatEvA EventPat | EPCatPunc | EPPlusPuncA | EPPlusPuncB | EPWild deriving (Eq,Ord,Show)

data OutputModifier = OId | AddCatEvA OutputModifier deriving (Eq,Ord,Show)

data ReadyElim = VarReadyElim String | Proj1ReadyElim ReadyElim {- these are fully-deriv'd elims: the next event you pull on the underlying channel has to be for for it.  -}
                    deriving (Eq,Ord,Show)

instance PrettyPrint ReadyElim where
    pp (VarReadyElim x) = x
    pp (Proj1ReadyElim el) = "pi1(" ++ pp el ++ ")"

computeReady :: Elim -> ReadyElim
computeReady (VarElim x) = VarReadyElim x
computeReady (Proj1Elim el) = Proj1ReadyElim (computeReady el)
computeReady (Proj2Elim el) = computeReady el

applyOutputModifier :: OutputModifier -> Event -> Event
applyOutputModifier OId = id
applyOutputModifier (AddCatEvA om) = CatEvA . applyOutputModifier om

data Action =
      SStop
    | SPrepareElim String [(EventPat,StateId)] -- state in which you chew off data for a the elim until it's ``ready''
    | SForwardInput ReadyElim OutputModifier [(EventPat,StateId)]
    | SOutput Event StateId
    | SBranch ReadyElim StateId StateId
    | SJump StateId
    deriving (Eq,Ord,Show)

addCatEvA SStop = SStop
addCatEvA a@(SPrepareElim {}) = a
addCatEvA (SForwardInput el om jt) = SForwardInput el (AddCatEvA om) jt
addCatEvA (SOutput ev j) = SOutput (CatEvA ev) j
addCatEvA a@(SBranch {}) = a
addCatEvA a@(SJump {}) = a

addCatEvAShape (SForwardInput el om jt) = SForwardInput el om (map (Data.Bifunctor.first EPCatEvA) jt)
addCatEvAShape (SPrepareElim x jt) = SPrepareElim x (map (Data.Bifunctor.first EPCatEvA) jt)
addCatEvAShape a@(SJump {}) = a
-- all other cases should be impossible, as this should only be used to build the forwarding tree.

data Autom = A { states :: Map.Map StateId Action } deriving (Eq,Ord,Show)

dumpAutom :: Autom -> String
dumpAutom (A m) = "digraph G {\n" ++ concatMap (uncurry go) (Map.assocs m) ++ "\n}"
    where
        go n SStop = show n ++ " : SStop" ++ "\n"
        go n (SPrepareElim x m) = concatMap (\(shp,n') -> show n ++ " -> " ++ show n' ++ "[label=\"prep " ++ show shp ++"\"]\n") m
        go n (SForwardInput el om m) = concatMap (\(shp,n') -> show n ++ " -> " ++ show n' ++ "[label=\"fwd " ++ show shp ++ " from " ++ pp el ++"\"]\n") m
        go n (SBranch el n1 n2) = (show n ++ " -> " ++ show n1 ++ "[label=\"branch A " ++ pp el ++ "\"]\n") ++ (show n ++ " -> " ++ show n2 ++ "[label=\"branch B" ++ pp el ++ "\"]\n")
        go n (SJump n') = show n ++ " -> " ++ show n' ++ "[label=\"j\"]" ++ "\n"
        go n (SOutput ev n') = show n ++ " -> " ++ show n' ++ "[label=\"output " ++ show ev ++ "\"]\n"
    

buildAutom :: ElimTerm -> (Int,Autom)
buildAutom e = let (init,states) = fst (runState (go (-1) e) (0,Nothing)) in (init,A states)
    where
        freshStateId :: State (Int,Maybe Int) Int
        freshStateId = do
            (n,mf) <- get
            put (n+1,mf)
            return n
        getFixStart :: State (Int,Maybe Int) Int
        getFixStart = do
            (n,mf) <- get
            return (fromMaybe (error "") mf)
        setFixStart f = do
            (n,mf) <- get
            put (n, Just f)
        eraseFixStart :: State (Int,Maybe Int) ()
        eraseFixStart = do { (n,_) <- get; put (n, Nothing)}

        jumpTo :: Int -> State (Int,Maybe Int) (Int,Map.Map Int Action)
        jumpTo addr = do { n <- freshStateId; return (n,Map.singleton n (SJump addr))}

        -- the forward tree basically computes the derivatives required in the states of the machine, rather than as an explicit piece of state.
        -- we unfold all possible derivative paths for the type, and jump to `end` when the type is null.
        -- This might not be the most efficient way to do this, but whatever.
        buildFwdTree _ TyEps end = jumpTo end
        buildFwdTree re TyInt end = do
            n <- freshStateId
            return (n, Map.singleton n (SForwardInput re OId [(EPIntEv,end)]))
        buildFwdTree re (TyCat s t) end = do
            puncForward <- freshStateId
            (sStart,ms) <- buildFwdTree re s puncForward
            let ms' = fmap (addCatEvA . addCatEvAShape) ms
            (tStart,mt) <- buildFwdTree re t end
            return (sStart, Map.union ms' (Map.insert puncForward (SForwardInput re OId [(EPCatPunc,tStart)]) mt))
        buildFwdTree re (TyPlus s t) end = do
            n <- freshStateId
            (sStart,ms) <- buildFwdTree re s end
            (tStart,mt) <- buildFwdTree re t end
            let jt = [(EPPlusPuncA,sStart),(EPPlusPuncB,tStart)]
            return (n,Map.insert n (SForwardInput re OId jt) (Map.union ms mt))
        {- forwardtree for a star type is cyclic, obviously. so the size of the graph should be neatly bounded. -}
        buildFwdTree re (TyStar s) end = do
            sStarStart <- freshStateId
            puncForward <- freshStateId
            (sStart,ms) <- buildFwdTree re s puncForward
            let ms' = fmap (addCatEvA . addCatEvAShape) ms
            let jt = [(EPPlusPuncA,end),(EPPlusPuncB,sStart)]
            let jt' = [(EPCatPunc,sStarStart)]
            return (sStarStart, Map.insert sStarStart (SForwardInput re OId jt) (Map.insert puncForward (SForwardInput re OId jt') ms'))
        
        {- this function seems to work but i have no idea how i wrote it -}
        buildPrepTree el@(VarElim {}) end k = k (jumpTo end)
        buildPrepTree (Proj1Elim el) end k = do
            (n,m) <- buildPrepTree el end k
            return (n, fmap addCatEvAShape m)
        buildPrepTree (Proj2Elim el) end k = do
            eatpi2 <- freshStateId
            buildPrepTree el eatpi2 (\doEl -> do
                (elStart,m) <- doEl
                let jumpTable = [(EPCatPunc,end),(EPCatEvA EPWild,eatpi2)]
                k (return (elStart, Map.insert eatpi2 (SPrepareElim (underlyingVar el) jumpTable) m))
             )


        go end EEpsR = jumpTo end
        go end (EUse elim ty) = do
            let readyElim = computeReady elim
            (fwdTreeStart,m) <- buildFwdTree readyElim ty end
            (prepStart,m') <- buildPrepTree elim fwdTreeStart id
            return (prepStart,Map.union m m')
        go end (EIntR k) = do
            n <- freshStateId
            return (n,Map.singleton n (SOutput (IntEv k) end))
        go end (ECatR e1 e2) = do
            puncNode <- freshStateId
            (e1start,m1) <- go puncNode e1
            (e2start,m2) <- go end e2
            let m1' = fmap addCatEvA m1
            return (e1start,Map.insert puncNode (SOutput CatPunc e2start) (Map.union m1' m2))
        go end (EInL e) = do
            puncNode <- freshStateId
            (estart,m) <- go end e
            return (puncNode,Map.insert puncNode (SOutput PlusPuncA estart) m)
        go end (EInR e) = do
            puncNode <- freshStateId
            (estart,m) <- go end e
            return (puncNode,Map.insert puncNode (SOutput PlusPuncB estart) m)
        
        go end (EPlusCase el e1 e2) = do
            n <- freshStateId
            (e1Start,m1) <- go end e1
            (e2Start,m2) <- go end e2
            let rel = computeReady el
            return (n,Map.insert n (SBranch rel e1Start e2Start) (Map.union m1 m2))


        go end (EFix e) = do
            fixStart <- freshStateId
            setFixStart fixStart
            (estart, m) <- go end e
            eraseFixStart
            return (fixStart, Map.insert fixStart (SJump estart) m)
        go end ERec = do
            recNode <- freshStateId
            fixAddr <- getFixStart
            return (recNode, Map.singleton recNode (SJump fixAddr))

underlyingVar :: Elim -> String
underlyingVar (VarElim x) = x
underlyingVar (Proj1Elim el) = underlyingVar el
underlyingVar (Proj2Elim el) = underlyingVar el


denoteAutom :: StateId -> Autom -> StreamFunc s TaggedEvent -> StreamFunc (s,Int) Event
denoteAutom n (A m) (SF x0 next_in) = SF (x0,n) go
    where
        go (x,n) = let action = Map.lookup n m in next x n (fromMaybe (error "") action)

        nextFromVar x' var =
            case next_in x' of
                Done -> Done
                Skip x'' -> Skip x''
                Yield (TEV z ev) x'' -> if z == var then Yield ev x'' else Skip x''

        nextFromReadyElim x' (VarReadyElim x) = nextFromVar x' x
        nextFromReadyElim x' (Proj1ReadyElim c) =
            case nextFromReadyElim x' c of
                Done -> Done
                Skip x'' -> Skip x''
                Yield (CatEvA ev) x'' -> Yield ev x''
                Yield {} -> error ""

        next x _ SStop = Done
        next x n (SPrepareElim var jumpTable) =
            case nextFromVar x var of
                Done -> Done
                Skip x' -> Skip (x',n)
                Yield ev x' ->
                    let jumpTarget = fromMaybe (error "") (lookupMatch ev jumpTable) in
                    Skip (x',jumpTarget)
        
        next x n (SForwardInput re om jumpTable) =
            case nextFromReadyElim x re of
                Done -> Done
                Skip x' -> Skip (x',n)
                Yield ev x' ->
                    let jumpTarget = fromMaybe (error "") (lookupMatch ev jumpTable) in
                    Yield (applyOutputModifier om ev) (x',jumpTarget)

        next x _ (SOutput ev n') = Yield ev (x,n')
        next x n (SBranch re t1 t2) =
            case nextFromReadyElim x re of
                Done -> Done
                Skip x' -> Skip (x',n)
                Yield PlusPuncA x' -> Skip (x',t1)
                Yield PlusPuncB x' -> Skip (x',t2)

        next x _ (SJump n') = Skip (x,n')

lookupMatch :: Event -> [(EventPat, StateId)] -> Maybe StateId
lookupMatch ev [] = Nothing
lookupmatch ev ((pat,n):pats) = if match ev pat then Just n else lookupMatch ev pats
    where
        match _ EPWild = True
        match (IntEv _) EPIntEv = True
        match (CatEvA ev) (EPCatEvA pat) = match ev pat
        match CatPunc EPCatPunc = True
        match PlusPuncA EPPlusPuncA = True
        match PlusPuncB EPPlusPuncB = True
        match _ _ = False