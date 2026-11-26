module FinScSpace.Dynamics.Evolution

import FinScBox.BoxInt
import FinScBox.Interfaces
import FinScBox.Box
import FinScBox.HereditaryMSet
import FinScBox.Views
import FinScBox.QuadraticExchange
import FinScBox.BlackRedZoom
import public FinScSpace.Geometry.Affine

%default total

--------------------------------------------------------------------------------
-- 1. DYNAMICS PARAMETERS, EVOLUTION STATE & DERIVED QUADRANCE REDUCTIONS
--------------------------------------------------------------------------------

public export
canonDecayNum : BoxInt
canonDecayNum = 7

public export
canonDecayDen : BoxInt
canonDecayDen = 32

public export
canonLoadCutDiv : BoxInt
canonLoadCutDiv = 16

public export
data StepMode
  = ModeLinear
  | ModeFactor Nat Nat

public export
Eq StepMode where
  ModeLinear       == ModeLinear       = True
  (ModeFactor a b) == (ModeFactor c d) = a == c && b == d
  _                == _                = False

public export
Show StepMode where
  show ModeLinear       = "ModeLinear"
  show (ModeFactor a b) = "ModeFactor(" ++ show a ++ ", " ++ show b ++ ")"

||| Parameter bundle governing local quadratic exchange, 1-hop load propagation, and Bresenham throttling:
||| - `dpMode`       : `ModeLinear` (`dpLagDiv = 0`) or `ModeFactor outerPasses innerTicks`
||| - `dpGenM0`      : Base Pythagorean generator `m_0 >= 2` (canonical `7` -> `(48, 14, 50)`)
||| - `dpLagDiv`     : Interaction-load threshold divisor (`<= 0` disables load accumulation)
||| - `dpLoadCutDiv` : Causal load truncation divisor relative to `dpLagDiv` (canonical `16`)
||| - `dpDecayNum`   : 1-hop retarded load retention numerator (canonical `7`)
||| - `dpDecayDen`   : 1-hop retarded load retention denominator (canonical `32`)
||| - `dpLinkCoup`   : Off-diagonal link-quadrance load coupling weight (canonical `1`)
public export
record DynamicsParams where
  constructor MkDynamicsParams
  dpMode       : StepMode
  dpGenM0      : BoxInt
  dpLagDiv     : BoxInt
  dpLoadCutDiv : BoxInt
  dpDecayNum   : BoxInt
  dpDecayDen   : BoxInt
  dpLinkCoup   : BoxInt

public export
Eq DynamicsParams where
  a == b =
    a.dpMode == b.dpMode &&
    a.dpGenM0 == b.dpGenM0 &&
    a.dpLagDiv == b.dpLagDiv &&
    a.dpLoadCutDiv == b.dpLoadCutDiv &&
    a.dpDecayNum == b.dpDecayNum &&
    a.dpDecayDen == b.dpDecayDen &&
    a.dpLinkCoup == b.dpLinkCoup

public export
Show DynamicsParams where
  show p =
    "DynamicsParams(mode=" ++ show p.dpMode ++
    ", m0=" ++ show p.dpGenM0 ++
    ", lagDiv=" ++ show p.dpLagDiv ++
    ", cutDiv=" ++ show p.dpLoadCutDiv ++
    ", decay=" ++ show p.dpDecayNum ++ "/" ++ show p.dpDecayDen ++
    ", coup=" ++ show p.dpLinkCoup ++ ")"

public export
canonDynamicsParams : StepMode -> DynamicsParams
canonDynamicsParams ModeLinear =
  MkDynamicsParams ModeLinear 7 0 canonLoadCutDiv canonDecayNum canonDecayDen 0
canonDynamicsParams mode@(ModeFactor _ _) =
  MkDynamicsParams mode 7 6000000 canonLoadCutDiv canonDecayNum canonDecayDen 1

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
Ord k => Eq (EvolutionState k) where
  a == b =
    a.polarityMaxel == b.polarityMaxel &&
    a.loadMaxel == b.loadMaxel &&
    a.throttleMaxel == b.throttleMaxel

public export
Show k => Show (EvolutionState k) where
  show s =
    "EvolutionState(pol=" ++ show s.polarityMaxel ++
    ", load=" ++ show s.loadMaxel ++
    ", thr=" ++ show s.throttleMaxel ++ ")"

||| Sterling recognition predicate certifying canonical AVL/half-storage invariants across all 3 `Maxel` channels.
public export
isCanonicalEvolutionState : Ord k => EvolutionState k -> Bool
isCanonicalEvolutionState st =
  isCanonicalMaxel st.polarityMaxel &&
  isCanonicalMaxel st.loadMaxel &&
  isCanonicalMaxel st.throttleMaxel

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

||| Total quadrance `2 * sum p(a)^2 + sum_{a < b} u_{ab}^2` via `sumStoredMaxel` of `quadranceOf pol`.
public export
stateQuadrance : Ord k => EvolutionState k -> BoxInt
stateQuadrance st = sumStoredMaxel (quadranceOf st.polarityMaxel)

public export
statePolarityNet : Ord k => EvolutionState k -> BoxInt
statePolarityNet st = traceMaxel st.polarityMaxel

public export
stateFluxNet : Ord k => EvolutionState k -> BoxInt
stateFluxNet st = sumStoredMaxel (toGeneralMaxel (offDiagMaxel st.polarityMaxel))

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
  (linkCoup : BoxInt) ->
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
                    else scaleM linkCoup fluxSq
  in siteSrc <+> linkSrc

||| Causal 1-hop retarded interaction-load step across arbitrary-dimension `unitSt` (`c = 1`, `SymForm`).
public export
stepCausalLoadMaxel :
  GroupCoord k =>
  (unitSt : Box BoxInt k) ->
  (lagDiv, loadCutDiv, decayNum, decayDen : BoxInt) ->
  (actSrcM : Maxel BoxInt k k SymForm) ->
  (oldLoad : Maxel BoxInt k k SymForm) ->
  Maxel BoxInt k k SymForm
stepCausalLoadMaxel unitSt lagDiv loadCutDiv decayNum decayDen actSrcM oldLoad =
  if lagDiv <= 0
    then emptyMaxel
    else
      let rawMin  = tdivPosBox lagDiv loadCutDiv
          minCut  = if rawMin < 1 then 1 else rawMin
          decayed = if isEmptyMaxel oldLoad || decayDen <= 0
                      then emptyMaxel
                      else scaleDivPruneMaxel decayDen minCut
                             (scaleM decayNum
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
Ord k => Eq (PacedPassAcc k) where
  a == b =
    a.ppPolarity == b.ppPolarity &&
    a.ppThrottle == b.ppThrottle &&
    a.ppYields == b.ppYields &&
    a.ppSkips == b.ppSkips

public export
Show k => Show (PacedPassAcc k) where
  show a =
    "PacedPassAcc(pol=" ++ show a.ppPolarity ++
    ", thr=" ++ show a.ppThrottle ++
    ", yields=" ++ show a.ppYields ++
    ", skips=" ++ show a.ppSkips ++ ")"

public export
paceMultiSubTicks : (subTicks : Nat) -> (budget, cost : BoxInt) -> BoxInt -> (Nat, Nat, BoxInt)
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
  (lagDiv, loadCutDiv, decayNum, decayDen, linkCoup, m0 : BoxInt) ->
  EvolutionState k ->
  (EvolutionState k, (Nat, Nat))
stepDynamicsCore ax outerPasses innerTicks lagDiv loadCutDiv decayNum decayDen linkCoup m0 st =
  if isEmptyMaxel st.polarityMaxel && isEmptyMaxel st.loadMaxel && isEmptyMaxel st.throttleMaxel
    then (st, (0, 0))
    else
      let kInt       = max 1 (cast (outerPasses * innerTicks))
          mSub       = if lagDiv > 0 then kInt * m0 else m0
          baseTriple = pythGeneratorTriple mSub
          fullTriple = powQuadraticTriple innerTicks baseTriple
          paceBudget = if lagDiv > 0 && m0 > 0 then m0 * lagDiv else 0
          axesBox    = activeAxisAtomsOf ax st.polarityMaxel
          unitSt     = activeUnitAxesOf ax st.polarityMaxel
          actSrc0    = activeQuadranceSource (lagDiv > 0) linkCoup st.polarityMaxel
          newLoad    = stepCausalLoadMaxel unitSt lagDiv loadCutDiv decayNum decayDen actSrc0 st.loadMaxel
          runPasses  : Nat -> PacedPassAcc k -> PacedPassAcc k
          runPasses Z acc = acc
          runPasses (S rem) acc =
            let acc1 = sweepCheckerboard ax axesBox (.ppPolarity)
                         (\posA, posB, pA, pB, uOld, a =>
                            let rawC  = if lagDiv <= 0 then 0 else linkLoadSum newLoad posA posB
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
    ModeLinear       => stepDynamicsCore ax 1  1  0          p.dpLoadCutDiv p.dpDecayNum p.dpDecayDen 0            p.dpGenM0 st
    ModeFactor oP iT => stepDynamicsCore ax oP iT p.dpLagDiv p.dpLoadCutDiv p.dpDecayNum p.dpDecayDen p.dpLinkCoup p.dpGenM0 st

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
0 prfBoundDipoleZeroNet :
  FinScSpace.Dynamics.Evolution.statePolarityNet
    (FinScSpace.Dynamics.Evolution.seedBoundDipole (FinScSpace.Geometry.Affine.spaceBasis {n = 2}) [0, 0] [0, 1] 10) = 0
prfBoundDipoleZeroNet = Refl

public export
0 prfQuadranceMaxelTotalMass :
  (let dp = FinScSpace.Dynamics.Evolution.seedBoundDipole (FinScSpace.Geometry.Affine.spaceBasis {n = 2}) [0, 0] [0, 1] 10
       qM = FinScSpace.Geometry.Affine.quadranceOf dp.polarityMaxel
   in (FinScBox.Box.sumStoredMaxel qM == MkBoxInt 400) &&
      (FinScSpace.Dynamics.Evolution.stateQuadrance dp == 400)) = True
prfQuadranceMaxelTotalMass = Refl

public export
0 prfBondFluxCausesDipoleSplit :
  (let r  = FinScBox.QuadraticExchange.exchangeQuadratic 7 0 0 50
       a1 = r.valA
       b1 = r.valB
       u1 = r.valU
   in (a1 == (-7)) && (b1 == 7) && (u1 == 48) &&
      (a1 + b1 == 0) &&
      (2 * (a1 * a1 + b1 * b1) + u1 * u1 == 2500)) = True
prfBondFluxCausesDipoleSplit = Refl

public export
0 prfExchangeQuadraticParam7 :
  (let r  = FinScBox.QuadraticExchange.exchangeQuadratic 7 100 (-43) 80
       a1 = r.valA
       b1 = r.valB
       u1 = r.valU
       q0 = 2 * (100 * 100 + (-43) * (-43)) + 80 * 80
       q1 = 2 * (a1 * a1 + b1 * b1) + u1 * u1
   in (a1 + b1 == 57) && (q1 <= q0)) = True
prfExchangeQuadraticParam7 = Refl

public export
0 prfExchangeQuadraticResonance :
  (let r1 = FinScBox.QuadraticExchange.exchangeQuadratic 7 7 0 24
       r2 = FinScBox.QuadraticExchange.exchangeQuadratic 7 0 7 (-24)
       a1 = r1.valA
       b1 = r1.valB
       u1 = r1.valU
       q0 = 2 * (7 * 7) + 24 * 24
       q1 = 2 * (a1 * a1 + b1 * b1) + u1 * u1
   in (a1 + b1 == 7) && (q1 <= q0) &&
      (r2.valA == r1.valB) && (r2.valB == r1.valA) && (r2.valU == negate u1)) = True
prfExchangeQuadraticResonance = Refl
