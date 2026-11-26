module FinScDynamics.Evolution

import FinScBox.BoxInt
import FinScBox.Interfaces
import FinScBox.Box
import FinScBox.HereditaryMSet
import FinScBox.Views
import FinScBox.QuadraticExchange
import FinScBox.BlackRedZoom

%default total

--------------------------------------------------------------------------------
-- 1. TIMELESS CONFIGURATION, EMERGENT AXIS ATOMS & DIRECTED EDGE KEYS
--------------------------------------------------------------------------------

||| Timeless snapshot of a physical multiset configuration (`PureMultiset` without `BoxInt` detail).
public export
Configuration : Type
Configuration = PureMultiset

||| Canonical positive scalar axis atom `{ [] : i + 1 }` (`0 -> X`, `1 -> Y`, `2 -> Z`, ...).
public export
axisAtom : Nat -> PureMultiset
axisAtom i = scalarKeyHMSet (natToInteger (S i))

||| If `k` is a positive scalar axis atom `{ [] : i }` (`i >= 1`), returns `Just i`.
public export
axisAtomIndex : PureMultiset -> Maybe Integer
axisAtomIndex (MkHMSet (BoxNode _ BoxLeaf (MkHMSet BoxLeaf) (MkBoxInt i) BoxLeaf)) =
  if i > 0 then Just i else Nothing
axisAtomIndex _ = Nothing

public export
atomToFin : {n : Nat} -> PureMultiset -> Maybe (Fin n)
atomToFin k =
  case axisAtomIndex k of
    Just i  => natToFin (integerToNat (i - 1)) n
    Nothing => Nothing

||| True iff `k` is an emergent positive scalar axis atom `{ [] : i }` (`i >= 1`).
public export
isAxisAtom : PureMultiset -> Bool
isAxisAtom k =
  case axisAtomIndex k of
    Just _  => True
    Nothing => False

||| True iff every key in `m` is an emergent spatial axis atom `{ [] : i }` (`i >= 1`, including `[]` at the origin).
public export
isSiteKey : PureMultiset -> Bool
isSiteKey (MkHMSet b) = allBox (\k, _ => isAxisAtom k) b

||| Projects any `Configuration` onto its spatial axis-atom components (`isSiteKey`-preserving, signed, ND).
public export
projectToSiteMSet : Configuration -> Configuration
projectToSiteMSet (MkHMSet b) = MkHMSet (filterBox isAxisAtom b)

||| Decodes a single-entry wrapped box `{ k : expectedW }` cleanly without allocation.
public export
extractSignedWrap : BoxInt -> PureMultiset -> Maybe PureMultiset
extractSignedWrap expectedW (MkHMSet (BoxNode _ BoxLeaf k w BoxLeaf)) =
  if w == expectedW then Just k else Nothing
extractSignedWrap _ _ = Nothing

||| Decodes `wrapBox k = { k : +1 }` back to `k`.
public export
extractWrapBox : PureMultiset -> Maybe PureMultiset
extractWrapBox = extractSignedWrap (MkBoxInt 1)

||| Extracts the unique key carrying multiplicity `expectedW` in `b`, or `Nothing` if absent/duplicated.
public export
extractUniqueSlot : BoxInt -> Box BoxInt PureMultiset -> Maybe PureMultiset
extractUniqueSlot expectedW b =
  case foldBox (\k, w, (cnt, res) =>
                  if w == expectedW then (S cnt, Just k) else (cnt, res))
               (0, Nothing) b of
    (1, Just k) => Just k
    _           => Nothing

||| Pure directed-edge key `{ wrapBox posA : +1, wrapBox posB : -1 }` inside `PureMultiset`.
public export
mkEdgeKey : (posA, posB : PureMultiset) -> PureMultiset
mkEdgeKey posA posB =
  MkHMSet $ setBox (wrapBox posB) (MkBoxInt (-1))
          $ singletonBox (wrapBox posA) (MkBoxInt 1)

||| Decoder for pure directed-edge keys `mkEdgeKey posA posB`.
public export
unpackEdgeKey : PureMultiset -> Maybe (PureMultiset, PureMultiset)
unpackEdgeKey entry@(MkHMSet b) =
  if isSiteKey entry || treeSizeNonZero b /= 2
    then Nothing
    else do
      kSrc <- extractUniqueSlot (MkBoxInt 1) b
      kDst <- extractUniqueSlot (MkBoxInt (-1)) b
      a    <- extractWrapBox kSrc
      d    <- extractWrapBox kDst
      if isSiteKey a && isSiteKey d && a /= d then Just (a, d) else Nothing

--------------------------------------------------------------------------------
-- 2. SPARSE POLARITY & QUADRANCE MAXELS + `Space n` & `PureMultiset` BASES
--------------------------------------------------------------------------------

||| Pure multiset spatial basis shared across `GroupCoord k` coordinates (`Space n` and `PureMultiset`).
public export
record AxisBasis (k : Type) where
  constructor MkAxisBasis
  baseAxes          : Box BoxInt PureMultiset
  allowEmergentAxes : Bool
  axisStep          : PureMultiset -> k
  isOddAxis         : PureMultiset -> k -> Bool
  toSiteMSet        : k -> PureMultiset
  fromSiteMSet      : PureMultiset -> k
  unitAxes          : Box BoxInt k

public export
mkPureCoord : {n : Nat} -> Space n -> Configuration
mkPureCoord =
  foldSpaceWithFin (\i, c, acc => acc <+> scaleM (signedToBoxInt c) (wrapBox (axisAtom (finToNat i)))) emptyHMSet

public export
coordAlong : AxisBasis k -> PureMultiset -> k -> Integer
coordAlong ax axKey pos = unwrapBox (lookupKeyHMSet axKey (ax.toSiteMSet pos))

public export
mkCoord : {n : Nat} -> AxisBasis k -> Space n -> k
mkCoord ax = ax.fromSiteMSet . mkPureCoord

public export
collectSiteAxisAtoms : PureMultiset -> Box BoxInt PureMultiset -> Box BoxInt PureMultiset
collectSiteAxisAtoms (MkHMSet b) acc0 =
  supportBox (acc0 <+> filterBox isAxisAtom b)

||| Unions `ax.baseAxes` with all emergent positive axis atoms `{ [] : i }` present in `pol`.
public export
activeAxisAtomsOf : AxisBasis k -> Maxel BoxInt k k DiagAntisymForm -> Box BoxInt PureMultiset
activeAxisAtomsOf ax pol =
  if not ax.allowEmergentAxes
    then ax.baseAxes
    else foldStoredMaxel
           (\a, b, _, acc =>
              collectSiteAxisAtoms (ax.toSiteMSet b)
                (collectSiteAxisAtoms (ax.toSiteMSet a) acc))
           ax.baseAxes pol

public export
activeUnitAxesOf : GroupCoord k => AxisBasis k -> Maxel BoxInt k k DiagAntisymForm -> Box BoxInt k
activeUnitAxesOf ax pol =
  if not ax.allowEmergentAxes
    then ax.unitAxes
    else
      let atoms = activeAxisAtomsOf ax pol
      in if atoms == ax.baseAxes
           then ax.unitAxes
           else unitStencilBox ax.axisStep atoms

||| Builds an `AxisBasis k` over any `GroupCoord k`.
public export
mkAxisBasis :
  GroupCoord k =>
  (allowEmergent : Bool) ->
  (axes          : Box BoxInt PureMultiset) ->
  (stepFn        : PureMultiset -> k) ->
  (oddFn         : PureMultiset -> k -> Bool) ->
  (toMSet        : k -> PureMultiset) ->
  (fromMSet      : PureMultiset -> k) ->
  AxisBasis k
mkAxisBasis allowEmergent axes stepFn oddFn toMSet fromMSet =
  MkAxisBasis axes allowEmergent stepFn oddFn toMSet fromMSet (unitStencilBox stepFn axes)

public export
baseAxesN : Nat -> Box BoxInt PureMultiset
baseAxesN Z     = BoxLeaf
baseAxesN (S k) = setBox (axisAtom k) (MkBoxInt 1) (baseAxesN k)

||| Dimension-uniform coordinate basis for `Space n` (`1D`, `2D`, `3D`, `ND`).
public export
spaceBasis : {n : Nat} -> AxisBasis (Space n)
spaceBasis {n} =
  mkAxisBasis
    False
    (baseAxesN n)
    (\axKey => maybe (zeroSpace n) unitSpace (atomToFin axKey))
    (\axKey, pos => maybe False (\i => isOddSigned (indexSpace i pos)) (atomToFin axKey))
    mkPureCoord
    (\m => tabulateSpace (\i => cast (lookupKeyHMSet (axisAtom (finToNat i)) m)))

public export
pureMSetBasis : Nat -> AxisBasis PureMultiset
pureMSetBasis dim =
  mkAxisBasis
    True
    (baseAxesN dim)
    wrapBox
    (\axKey, pos => isOddBox (lookupKeyHMSet axKey pos))
    id
    projectToSiteMSet

--------------------------------------------------------------------------------
-- 3. DYNAMICS PARAMETERS, EVOLUTION STATE & DERIVED QUADRANCE REDUCTIONS
--------------------------------------------------------------------------------

public export
canonDecayNum : Integer
canonDecayNum = 7

public export
canonDecayDen : Integer
canonDecayDen = 32

public export
data StepMode
  = ModeLinear
  | ModeFactor Nat Nat

||| Parameter bundle governing local quadratic exchange, 1-hop load propagation, and Bresenham throttling:
||| - `dpMode`     : `ModeLinear` (`dpLagDiv = 0`) or `ModeFactor outerPasses innerTicks`
||| - `dpGenM0`    : Base Pythagorean generator `m_0 >= 2` (canonical `7` -> `(48, 14, 50)`)
||| - `dpLagDiv`   : Interaction-load threshold divisor (`<= 0` disables load accumulation)
||| - `dpDecayNum` : 1-hop retarded load retention numerator (canonical `7`)
||| - `dpDecayDen` : 1-hop retarded load retention denominator (canonical `32`)
||| - `dpLinkCoup` : Off-diagonal link-quadrance load coupling weight (canonical `1`)
public export
record DynamicsParams where
  constructor MkDynamicsParams
  dpMode     : StepMode
  dpGenM0    : Integer
  dpLagDiv   : Integer
  dpDecayNum : Integer
  dpDecayDen : Integer
  dpLinkCoup : Integer

public export
canonDynamicsParams : StepMode -> DynamicsParams
canonDynamicsParams ModeLinear =
  MkDynamicsParams ModeLinear 7 0 canonDecayNum canonDecayDen 0
canonDynamicsParams mode@(ModeFactor _ _) =
  MkDynamicsParams mode 7 6000000 canonDecayNum canonDecayDen 1

||| Blind local evolution state over any discrete coordinate basis `k`:
||| - `polarityMaxel` : half-stored diagonal site polarity + antisymmetric edge flux (`DiagAntisymForm`)
||| - `loadMaxel`     : causal 1-hop retarded interaction load (`SymForm`) propagating at `c = 1`
||| - `throttleMaxel` : sparse integer Bresenham pacing accumulator (`SymForm`, pruned at `0`)
public export
record EvolutionState (k : Type) where
  constructor MkEvolutionState
  polarityMaxel : Maxel BoxInt k k DiagAntisymForm
  loadMaxel     : Maxel BoxInt k k SymForm
  throttleMaxel : Maxel BoxInt k k SymForm

public export
Ord k => Semigroup (EvolutionState k) where
  (<+>) a b =
    MkEvolutionState
      (a.polarityMaxel <+> b.polarityMaxel)
      (a.loadMaxel <+> b.loadMaxel)
      (a.throttleMaxel <+> b.throttleMaxel)

public export
Ord k => Monoid (EvolutionState k) where
  neutral = MkEvolutionState emptyMaxel emptyMaxel emptyMaxel

public export
Ord k => MultisetAlgebra BoxInt (EvolutionState k) where
  zeroM  = neutral
  addM   = (<+>)
  negM s = MkEvolutionState (negM s.polarityMaxel) (negM s.loadMaxel) (negM s.throttleMaxel)
  subM a b =
    MkEvolutionState
      (subM a.polarityMaxel b.polarityMaxel)
      (subM a.loadMaxel b.loadMaxel)
      (subM a.throttleMaxel b.throttleMaxel)
  scaleM c s =
    MkEvolutionState
      (scaleM c s.polarityMaxel)
      (scaleM c s.loadMaxel)
      (scaleM c s.throttleMaxel)
  dotM a b =
    (a.polarityMaxel <.> b.polarityMaxel) +
    (a.loadMaxel <.> b.loadMaxel) +
    (a.throttleMaxel <.> b.throttleMaxel)

||| Canonical symmetric quadrance `Maxel` (`SymForm`) of `pol : Maxel BoxInt k k DiagAntisymForm`:
||| diagonal `(a, a)` holds `2 * p(a)^2` and off-diagonal `(a, b)` (`a < b`) holds `u_{ab}^2`.
public export
quadranceOf : Ord k => Maxel BoxInt k k DiagAntisymForm -> Maxel BoxInt k k SymForm
quadranceOf pol =
  let pSq = pol .*. pol
  in pSq <+> diagEmbedMaxel (diagBox pSq)

||| Total quadrance `2 * sum p(a)^2 + sum_{a < b} u_{ab}^2` via `sumStoredMaxel` of `quadranceOf pol`.
public export
stateQuadrance : Ord k => EvolutionState k -> Integer
stateQuadrance st = unwrapBox (sumStoredMaxel (quadranceOf st.polarityMaxel))

public export
statePolarityNet : Ord k => EvolutionState k -> Integer
statePolarityNet st = unwrapBox (traceMaxel st.polarityMaxel)

public export
stateFluxNet : Ord k => EvolutionState k -> Integer
stateFluxNet st = unwrapBox (sumStoredMaxel (toGeneralMaxel (offDiagMaxel st.polarityMaxel)))

public export
stateFluxAntisym : Ord k => EvolutionState k -> Bool
stateFluxAntisym st = isAntisymMaxel (offDiagMaxel st.polarityMaxel)

public export
stateLoadSym : Ord k => EvolutionState k -> Bool
stateLoadSym st = isSymMaxel st.loadMaxel

public export
stateActiveWork : Ord k => EvolutionState k -> Nat
stateActiveWork st =
  maxelNodeCount st.polarityMaxel + maxelNodeCount st.loadMaxel + maxelNodeCount st.throttleMaxel

--------------------------------------------------------------------------------
-- 4. BALANCED ZERO-SUM EXCITATIONS & BOUND DIPOLES (ND OVER `Vect n`)
--------------------------------------------------------------------------------

public export
seedDipoleSites : Ord k => (pPos, pNeg : k) -> (amp : BoxInt) -> EvolutionState k
seedDipoleSites pPos pNeg amp =
  let w = addAtMaxelEdge pNeg pNeg (negate amp) (singletonMaxelEdge pPos pPos amp)
  in MkEvolutionState w emptyMaxel emptyMaxel

||| Seeds an oscillating bound polarity dipole (`+amp` at `posVec`, `-amp` at `negVec`).
public export
seedBoundDipole : {n : Nat} -> Ord k => AxisBasis k -> (posVec, negVec : Space n) -> (amp : BoxInt) -> EvolutionState k
seedBoundDipole ax posVec negVec amp =
  seedDipoleSites (mkCoord ax posVec) (mkCoord ax negVec) amp

public export
transverseEnv4 : Ord k => (SignedCoord -> k) -> (t0 : SignedCoord) -> (halfA, fullA : BoxInt) -> Box BoxInt k
transverseEnv4 mkAxisCoord t0 halfA fullA =
  addAtKeyBox (mkAxisCoord (t0 - 1)) halfA $
  addAtKeyBox (mkAxisCoord t0)       fullA $
  addAtKeyBox (mkAxisCoord (t0 + 1)) fullA $
  singletonBox (mkAxisCoord (t0 + 2)) halfA

||| Balanced zero-sum 4-layer directed pulse propagating along `+X` with envelope along `transAxis`.
public export
seedDirectedPulse :
  {n : Nat} ->
  MonoidCoord k =>
  AxisBasis k ->
  (center : Space (S n)) ->
  (transAxis : Fin (S n)) ->
  (amp : BoxInt) ->
  EvolutionState k
seedDirectedPulse ax center@(x0 :: rest) transAxis amp =
  let t0        = indexSpace transAxis center
      baseTrans = ZeroZ :: rest
      halfA     = tdiv2Box amp
      tEnv      = transverseEnv4 (\t => mkCoord ax (replaceSpace transAxis t baseTrans)) t0 halfA amp
      e1        = mkCoord ax (the (Space 1) [x0 - 2])
      e2        = mkCoord ax (the (Space 1) [x0 - 1])
      e3        = mkCoord ax (the (Space 1) [x0])
      e4        = mkCoord ax (the (Space 1) [x0 + 1])
      e5        = mkCoord ax (the (Space 1) [x0 + 2])
      rowPol    = setMaxelEdge e2 e2 (MkBoxInt (-1)) $
                  setMaxelEdge e4 e4 (MkBoxInt 1)    $
                  setMaxelEdge e1 e2 (MkBoxInt (-2)) $
                  setMaxelEdge e2 e3 (MkBoxInt (-2)) $
                  setMaxelEdge e3 e4 (MkBoxInt 2)    $
                  singletonMaxelEdge e4 e5 (MkBoxInt 2)
  in MkEvolutionState (shiftConvolveMaxel rowPol tEnv) emptyMaxel emptyMaxel

||| Seeds a balanced zero-sum antisymmetric directed-edge flux link `srcVec -> dstVec` with weight `u`.
public export
seedEdgeFlux : {n : Nat} -> Ord k => AxisBasis k -> (srcVec, dstVec : Space n) -> (u : BoxInt) -> EvolutionState k
seedEdgeFlux ax srcVec dstVec u =
  MkEvolutionState (singletonMaxelEdge (mkCoord ax srcVec) (mkCoord ax dstVec) u) emptyMaxel emptyMaxel

--------------------------------------------------------------------------------
-- 5. CAUSAL 1-HOP INTERACTION LOAD & ENDOGENOUS BRESENHAM THROTTLING
--------------------------------------------------------------------------------

||| Causal 1-hop symmetric quadrance `Maxel` source derived directly from `qM = quadranceOf pol`.
public export
activeQuadranceSource :
  Ord k =>
  Bool ->
  (linkCoup : Integer) ->
  (pol : Maxel BoxInt k k DiagAntisymForm) ->
  Maxel BoxInt k k SymForm
activeQuadranceSource False _        _   = emptyMaxel
activeQuadranceSource True  linkCoup pol =
  let qM      = quadranceOf pol
      fluxSq  = offDiagMaxel qM
      incU2   = scaleDivPruneBox 2 1 (contractRMaxel (toGeneralMaxel fluxSq))
      siteSrc = diagEmbedMaxel (diagBox qM <+> incU2)
      linkSrc = if linkCoup <= 0
                  then emptyMaxel
                  else if linkCoup == 1
                    then fluxSq
                    else scaleM (MkBoxInt linkCoup) fluxSq
  in siteSrc <+> linkSrc

||| Causal 1-hop retarded interaction-load step across arbitrary-dimension `unitSt` (`c = 1`, `SymForm`).
public export
stepCausalLoadMaxel :
  GroupCoord k =>
  (unitSt : Box BoxInt k) ->
  (lagDiv, decayNum, decayDen : Integer) ->
  (actSrcM : Maxel BoxInt k k SymForm) ->
  (oldLoad : Maxel BoxInt k k SymForm) ->
  Maxel BoxInt k k SymForm
stepCausalLoadMaxel unitSt lagDiv decayNum decayDen actSrcM oldLoad =
  if lagDiv <= 0
    then emptyMaxel
    else
      let rawMin  = divIntegerPos lagDiv 16
          minCut  = if rawMin < 1 then 1 else rawMin
          decayed = if isEmptyMaxel oldLoad || decayDen <= 0
                      then emptyMaxel
                      else scaleDivPruneMaxel decayDen minCut
                             (scaleM (MkBoxInt decayNum)
                                (shiftConvolveMaxel oldLoad unitSt))
      in decayed <+> pruneMinMaxel minCut actSrcM

||| Canonical start vertex `s` when `(a, b)` spans an undirected step along `stepDir`.
public export
canonLinkStart : GroupCoord k => k -> k -> k -> Maybe k
canonLinkStart stepDir a b =
  if b == combine a stepDir then Just a
  else if a == combine b stepDir then Just b
  else Nothing

||| Collects strictly active canonical links `(s, s + stepDir)` touching non-zero sites or edges of `pol`.
public export
collectAxisLinks : GroupCoord k => k -> Maxel BoxInt k k DiagAntisymForm -> Box BoxInt k
collectAxisLinks stepDir pol =
  foldStoredMaxel
    (\a, b, _, acc =>
       if a == b
         then setBox a (MkBoxInt 1) (setBox (coordSub a stepDir) (MkBoxInt 1) acc)
         else case canonLinkStart stepDir a b of
                Just s  => setBox s (MkBoxInt 1) acc
                Nothing => acc)
    BoxLeaf
    pol

public export
applyLinkExchangeTriple :
  Ord k =>
  QuadraticTriple ->
  (posA, posB : k) ->
  (pA, pB, uOld : BoxInt) ->
  Maxel BoxInt k k DiagAntisymForm ->
  Maxel BoxInt k k DiagAntisymForm
applyLinkExchangeTriple qt posA posB pA pB uOld pol =
  let res = exchangeQuadraticTriple qt pA pB uOld
      w1  = if res.valA /= pA then setMaxelEdge posA posA res.valA pol else pol
      w2  = if res.valB /= pB then setMaxelEdge posB posB res.valB w1  else w1
  in if res.valU /= uOld then setMaxelEdge posA posB res.valU w2 else w2

public export
linkLoadSum : Ord k => Maxel BoxInt k k SymForm -> k -> k -> BoxInt
linkLoadSum loadM posA posB =
  lookupMaxel posA posA loadM + lookupMaxel posB posB loadM + lookupMaxel posA posB loadM

public export
sweepAxisPass :
  GroupCoord k =>
  (stepDir : k) ->
  (wantOdd : Bool) ->
  (isOddFn : k -> Bool) ->
  (linksBox : Box BoxInt k) ->
  (getPol : acc -> Maxel BoxInt k k DiagAntisymForm) ->
  (onLink : k -> k -> BoxInt -> BoxInt -> BoxInt -> acc -> acc) ->
  acc ->
  acc
sweepAxisPass stepDir wantOdd isOddFn linksBox getPol onLink initAcc =
  foldBox (\posA, _, acc =>
             if isOddFn posA /= wantOdd
               then acc
               else
                 let posB = combine posA stepDir
                     pol  = getPol acc
                     pA   = lookupMaxel posA posA pol
                     pB   = lookupMaxel posB posB pol
                     uOld = lookupMaxel posA posB pol
                 in if pA == pB && boxIsZero uOld
                      then acc
                      else onLink posA posB pA pB uOld acc)
          initAcc
          linksBox

||| Arbitrary-dimension checkerboard link sweep folding directly over `axesBox : Box BoxInt PureMultiset`.
public export
sweepCheckerboard :
  GroupCoord k =>
  AxisBasis k ->
  Box BoxInt PureMultiset ->
  (getPol : acc -> Maxel BoxInt k k DiagAntisymForm) ->
  (onLink : k -> k -> BoxInt -> BoxInt -> BoxInt -> acc -> acc) ->
  acc ->
  acc
sweepCheckerboard ax axesBox getPol onLink acc0 =
  foldBox (\axKey, _, acc =>
             let stepDir = ax.axisStep axKey
                 isOddFn = ax.isOddAxis axKey
                 links   = collectAxisLinks stepDir (getPol acc)
                 accE    = sweepAxisPass stepDir False isOddFn links getPol onLink acc
             in sweepAxisPass stepDir True isOddFn links getPol onLink accE)
          acc0
          axesBox

public export
record PacedPassAcc (k : Type) where
  constructor MkPacedPassAcc
  ppPolarity : Maxel BoxInt k k DiagAntisymForm
  ppThrottle : Maxel BoxInt k k SymForm
  ppYields   : Nat
  ppSkips    : Nat

public export
paceMultiSubTicks : (subTicks : Nat) -> (budget, cost : Integer) -> BoxInt -> (Nat, Nat, BoxInt)
paceMultiSubTicks Z _ _ bal = (0, 0, bal)
paceMultiSubTicks (S rem) budget cost bal =
  let (step, bal1)   = paceStreamStep budget cost bal
      (yR, sR, balF) = paceMultiSubTicks rem budget cost bal1
  in case step of
       StreamSkip    => (yR, S sR, balF)
       StreamDone    => (yR, sR, balF)
       StreamYield _ => (S yR, sR, balF)

||| Blind local `StreamSkip`/`StreamYield` evolution stepper parameterized by `(outerPasses, innerTicks)`.
public export
stepDynamicsCore :
  GroupCoord k =>
  AxisBasis k ->
  (outerPasses, innerTicks : Nat) ->
  (lagDiv, decayNum, decayDen, linkCoup, m0 : Integer) ->
  EvolutionState k ->
  (EvolutionState k, (Nat, Nat))
stepDynamicsCore ax outerPasses innerTicks lagDiv decayNum decayDen linkCoup m0 st =
  if isEmptyMaxel st.polarityMaxel && isEmptyMaxel st.loadMaxel && isEmptyMaxel st.throttleMaxel
    then (st, (0, 0))
    else
      let kInt       = max 1 (natToInteger (outerPasses * innerTicks))
          mSub       = if lagDiv > 0 then kInt * m0 else m0
          baseTriple = pythGeneratorTriple (MkBoxInt mSub)
          fullTriple = powQuadraticTriple innerTicks baseTriple
          paceBudget = if lagDiv > 0 && m0 > 0 then m0 * lagDiv else 0
          axesBox    = activeAxisAtomsOf ax st.polarityMaxel
          unitSt     = activeUnitAxesOf ax st.polarityMaxel
          actSrc0    = activeQuadranceSource (lagDiv > 0) linkCoup st.polarityMaxel
          newLoad    = stepCausalLoadMaxel unitSt lagDiv decayNum decayDen actSrc0 st.loadMaxel
          runPasses  : Nat -> PacedPassAcc k -> PacedPassAcc k
          runPasses Z acc = acc
          runPasses (S rem) acc =
            let acc1 = sweepCheckerboard ax axesBox (.ppPolarity)
                         (\posA, posB, pA, pB, uOld, a =>
                            let rawC  = if lagDiv <= 0 then 0 else unwrapBox (linkLoadSum newLoad posA posB)
                                cost  = if rawC < lagDiv then 0 else rawC
                                bal   = lookupMaxel posA posB a.ppThrottle
                                (yCnt, sCnt, newBal) = paceMultiSubTicks innerTicks paceBudget cost bal
                                thr1  = if newBal /= bal then setMaxelEdge posA posB newBal a.ppThrottle else a.ppThrottle
                                pol1  = if yCnt == 0
                                          then a.ppPolarity
                                          else let qt = if yCnt == innerTicks then fullTriple
                                                        else if yCnt == 1 then baseTriple
                                                        else powQuadraticTriple yCnt baseTriple
                                               in applyLinkExchangeTriple qt posA posB pA pB uOld a.ppPolarity
                            in MkPacedPassAcc pol1 thr1 (a.ppYields + yCnt) (a.ppSkips + sCnt))
                         acc
            in runPasses rem acc1
          pFin       = runPasses outerPasses (MkPacedPassAcc st.polarityMaxel st.throttleMaxel 0 0)
      in (MkEvolutionState pFin.ppPolarity newLoad pFin.ppThrottle, (pFin.ppYields, pFin.ppSkips))

||| Evaluates one blind evolution step under explicit `DynamicsParams`.
public export
stepDynamicsWith :
  GroupCoord k =>
  AxisBasis k ->
  DynamicsParams ->
  EvolutionState k ->
  (EvolutionState k, (Nat, Nat))
stepDynamicsWith ax p st =
  case p.dpMode of
    ModeLinear       => stepDynamicsCore ax 1  1  0          p.dpDecayNum p.dpDecayDen 0            p.dpGenM0 st
    ModeFactor oP iT => stepDynamicsCore ax oP iT p.dpLagDiv p.dpDecayNum p.dpDecayDen p.dpLinkCoup p.dpGenM0 st

||| Single streaming step over `EvolutionState k` charging `GohBound` only on `StreamYield`.
public export
stepDynamicsStreamWith :
  GroupCoord k =>
  AxisBasis k ->
  DynamicsParams ->
  EvolutionState k ->
  (StreamStep (EvolutionState k), Nat, Nat)
stepDynamicsStreamWith ax params st =
  let (st1, (yStep, sStep)) = stepDynamicsWith ax params st
  in if yStep == 0
       then if sStep == 0
              then (StreamDone, 0, 0)
              else (StreamSkip, 0, sStep)
       else (StreamYield st1, yStep, sStep)

||| Injects any peeled `Configuration` relic key `k` (directed edge `mkEdgeKey a b` or site key `s`)
||| directly over `AxisBasis k` with flux weight `amp` — preserving negative coordinates and 3D/ND axes
||| with zero `(Nat, Nat, Nat)` tuple conversion.
public export
injectRelicBond : GroupCoord k => AxisBasis k -> EvolutionState k -> Configuration -> BoxInt -> EvolutionState k
injectRelicBond ax u k amp =
  let (posA, posB) =
        case unpackEdgeKey k of
          Just (a, b) => (ax.fromSiteMSet a, ax.fromSiteMSet b)
          Nothing     =>
            let s = ax.fromSiteMSet (projectToSiteMSet k)
            in (s, combine s (ax.axisStep (axisAtom 0)))
  in u <+> MkEvolutionState (singletonMaxelEdge posA posB amp) emptyMaxel emptyMaxel

||| Coupled two-multiset boundary flow parameterized by `DynamicsParams`:
||| external reservoir `eSrc : Configuration` peels 1 bond quantum (`qAmp`, quadrance `qAmp^2`) per tick
||| into `u : EvolutionState k` via `viewAsAntiBox eSrc`, decoupling into closed evolution once `eSrc == []`.
public export
stepCoupledSourceFlow :
  GroupCoord k =>
  AxisBasis k ->
  DynamicsParams ->
  (qAmp : BoxInt) ->
  (EvolutionState k, Configuration) ->
  (StreamStep (EvolutionState k, Configuration), Nat, Nat)
stepCoupledSourceFlow ax params qAmp (u, eSrc) =
  let (uIn, nextSrc) =
        case viewAsAntiBox eSrc of
          EmptyVacuum       => (u, emptyHMSet)
          PopBlackBox k rst => (injectRelicBond ax u k qAmp, rst)
          PopRedBox   k rst => (injectRelicBond ax u k (negate qAmp), rst)
      (uNext, (yStep, sStep)) = stepDynamicsWith ax params uIn
  in if yStep == 0 && sStep == 0 && nextSrc == emptyHMSet
       then (StreamDone, 0, 0)
       else (StreamYield (uNext, nextSrc), max 1 yStep, sStep)

||| Active bidirectional coupling of two evolving `EvolutionState k` universes `(uA, uB)` under `DynamicsParams`
||| across any `seam : Maxel BoxInt k k DiagAntisymForm` boundary mask (`maskByMaxel`, zero global oracle).
public export
stepCoupledUniversePair :
  GroupCoord k =>
  AxisBasis k ->
  DynamicsParams ->
  (seam : Maxel BoxInt k k DiagAntisymForm) ->
  (qAmp : BoxInt) ->
  (EvolutionState k, EvolutionState k) ->
  (StreamStep (EvolutionState k, EvolutionState k), Nat, Nat)
stepCoupledUniversePair ax params seam qAmp (uA, uB) =
  let clampQ   = \w =>
        if w >= qAmp then qAmp
        else if w <= negate qAmp then negate qAmp
        else tdiv2Box w
      deltaPol = mapPruneMaxel clampQ (maskByMaxel (subM uA.polarityMaxel uB.polarityMaxel) seam)
      deltaSt  = MkEvolutionState deltaPol emptyMaxel emptyMaxel
      (nA, (yA, sA)) = stepDynamicsWith ax params (subM uA deltaSt)
      (nB, (yB, sB)) = stepDynamicsWith ax params (uB <+> deltaSt)
  in if yA + yB == 0 && sA + sB == 0
       then (StreamDone, 0, 0)
       else (StreamYield (nA, nB), max 1 (yA + yB), sA + sB)

--------------------------------------------------------------------------------
-- 6. COMPILE-TIME QTT 0 ALGEBRAIC INVARIANTS
--------------------------------------------------------------------------------

public export
0 prfAntisymSingleEdge :
  (let p0 : Space 2
       p0 = [0, 0]
       p1 : Space 2
       p1 = [1, 0]
       e  = FinScBox.Box.singletonMaxelEdge {form = AntisymForm} p0 p1 (MkBoxInt 12)
   in (FinScBox.Box.maxelNodeCount e == 1) &&
      (FinScBox.Box.traceMaxel e == MkBoxInt 0) &&
      (FinScBox.Box.lookupMaxel p1 p0 e == MkBoxInt (-12))) = True
prfAntisymSingleEdge = Refl

public export
0 prfBoundDipoleZeroNet :
  FinScDynamics.Evolution.statePolarityNet
    (FinScDynamics.Evolution.seedBoundDipole (FinScDynamics.Evolution.spaceBasis {n = 2}) [0, 0] [0, 1] 10) = 0
prfBoundDipoleZeroNet = Refl

public export
0 prfQuadranceMaxelTotalMass :
  (let dp = FinScDynamics.Evolution.seedBoundDipole (FinScDynamics.Evolution.spaceBasis {n = 2}) [0, 0] [0, 1] 10
       qM = FinScDynamics.Evolution.quadranceOf dp.polarityMaxel
   in (FinScBox.Box.sumStoredMaxel qM == MkBoxInt 400) &&
      (FinScDynamics.Evolution.stateQuadrance dp == 400)) = True
prfQuadranceMaxelTotalMass = Refl

public export
0 prfBondFluxCausesDipoleSplit :
  (let r  = FinScBox.QuadraticExchange.exchangeQuadratic (MkBoxInt 7) (MkBoxInt 0) (MkBoxInt 0) (MkBoxInt 50)
       a1 = unwrapBox r.valA
       b1 = unwrapBox r.valB
       u1 = unwrapBox r.valU
   in (a1 == (-7)) && (b1 == 7) && (u1 == 48) &&
      (a1 + b1 == 0) &&
      (2 * (a1 * a1 + b1 * b1) + u1 * u1 == 2500)) = True
prfBondFluxCausesDipoleSplit = Refl

public export
0 prfExchangeQuadraticParam7 :
  (let r  = FinScBox.QuadraticExchange.exchangeQuadratic (MkBoxInt 7) (MkBoxInt 100) (MkBoxInt (-43)) (MkBoxInt 80)
       a1 = unwrapBox r.valA
       b1 = unwrapBox r.valB
       u1 = unwrapBox r.valU
       q0 = 2 * (100 * 100 + (-43) * (-43)) + 80 * 80
       q1 = 2 * (a1 * a1 + b1 * b1) + u1 * u1
   in (a1 + b1 == 57) && (q1 <= q0)) = True
prfExchangeQuadraticParam7 = Refl

public export
0 prfExchangeQuadraticResonance :
  (let r1 = FinScBox.QuadraticExchange.exchangeQuadratic (MkBoxInt 7) (MkBoxInt 7) (MkBoxInt 0) (MkBoxInt 24)
       r2 = FinScBox.QuadraticExchange.exchangeQuadratic (MkBoxInt 7) (MkBoxInt 0) (MkBoxInt 7) (MkBoxInt (-24))
       a1 = unwrapBox r1.valA
       b1 = unwrapBox r1.valB
       u1 = unwrapBox r1.valU
       q0 = 2 * (7 * 7) + 24 * 24
       q1 = 2 * (a1 * a1 + b1 * b1) + u1 * u1
   in (a1 + b1 == 7) && (q1 <= q0) &&
      (r2.valA == r1.valB) && (r2.valB == r1.valA) && (unwrapBox r2.valU == -u1)) = True
prfExchangeQuadraticResonance = Refl

public export
0 prfPureStepShift :
  FinScDynamics.Evolution.mkPureCoord [-8, 7, -3] + wrapBox (FinScDynamics.Evolution.axisAtom 0)
  = FinScDynamics.Evolution.mkPureCoord [-7, 7, -3]
prfPureStepShift = Refl

public export
0 prfEdgeKeyRoundTrip :
  (let pA = mkPureCoord [-2, 5, 1]
       pB = mkPureCoord [-1, 5, 1]
       k  = mkEdgeKey pA pB
   in case unpackEdgeKey k of
        Just (a, b) => (a == pA) && (b == pB)
        Nothing     => False) = True
prfEdgeKeyRoundTrip = Refl
