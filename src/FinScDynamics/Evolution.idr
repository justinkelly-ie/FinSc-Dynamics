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

public export
axisX : PureMultiset
axisX = scalarKeyHMSet 1

public export
axisY : PureMultiset
axisY = scalarKeyHMSet 2

public export
axisZ : PureMultiset
axisZ = scalarKeyHMSet 3

||| Unit coordinate shifts strictly inside `PureMultiset` (zero tuple conversion).
public export
stepX : PureMultiset
stepX = wrapBox axisX

public export
stepZ : PureMultiset
stepZ = wrapBox axisZ

public export
isNothingMaybe : Maybe a -> Bool
isNothingMaybe Nothing = True
isNothingMaybe _       = False

||| If `k` is a positive scalar axis atom `{ [] : i }` (`i >= 1`), returns `Just i`.
public export
axisAtomIndex : PureMultiset -> Maybe Integer
axisAtomIndex (MkHMSet (BoxNode _ BoxLeaf (MkHMSet BoxLeaf) (MkBoxInt i) BoxLeaf)) =
  if i > 0 then Just i else Nothing
axisAtomIndex _ = Nothing

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
-- 2. SPARSE POLARITY & QUADRANCE MAXELS + 2D, 3D & ND COORDINATE BASES
--------------------------------------------------------------------------------

public export
Coord2 : Type
Coord2 = (SignedCoord, SignedCoord)

public export
Coord3 : Type
Coord3 = (SignedCoord, (SignedCoord, SignedCoord))

||| Active signed polarity carrier (`DiagAntisymForm`):
||| diagonal `(a, a)` holds site polarity (+ Black / - Red) and off-diagonal `(a, b)`
||| holds antisymmetric directed link flux `u_{ab} = -u_{ba}`.
public export
PolarityMaxel : Type -> Type
PolarityMaxel k = Maxel BoxInt k k DiagAntisymForm

||| Symmetric quadrance carrier (`SymForm`) produced by `pol .*. pol`:
||| diagonal `(a, a)` holds site quadrance `2 * p(a)^2` and off-diagonal `(a, b)` (`a < b`)
||| holds undirected link quadrance `u_{ab}^2`.
public export
QuadranceMaxel : Type -> Type
QuadranceMaxel k = Maxel BoxInt k k SymForm

||| Pure multiset spatial basis shared across `Coord2`, `Coord3`, and `PureMultiset`.
public export
record AxisBasis (k : Type) where
  constructor MkAxisBasis
  baseAxes          : Box BoxInt PureMultiset
  allowEmergentAxes : Bool
  axisStep          : PureMultiset -> k
  isOddAxis         : PureMultiset -> k -> Bool
  shiftAdd          : k -> k -> k
  shiftSub          : k -> k -> k
  toSiteMSet        : k -> PureMultiset
  fromSiteMSet      : PureMultiset -> k
  unitAxes          : Box BoxInt k

public export
mkPureCoord2D : (x, y : Integer) -> Configuration
mkPureCoord2D x y =
  MkHMSet $ addAtKeyBox axisY (MkBoxInt y)
          $ addAtKeyBox axisX (MkBoxInt x) BoxLeaf

public export
mkPureCoord3D : (x, y, z : Integer) -> Configuration
mkPureCoord3D x y z =
  MkHMSet $ addAtKeyBox axisZ (MkBoxInt z)
          $ addAtKeyBox axisY (MkBoxInt y)
          $ addAtKeyBox axisX (MkBoxInt x) BoxLeaf

public export
coordAlong : AxisBasis k -> PureMultiset -> k -> Integer
coordAlong ax axKey pos = unwrapBox (lookupKeyHMSet axKey (ax.toSiteMSet pos))

public export
mkCoord2D : AxisBasis k -> Integer -> Integer -> k
mkCoord2D ax x y = ax.fromSiteMSet (mkPureCoord2D x y)

public export
mkCoord3D : AxisBasis k -> Integer -> Integer -> Integer -> k
mkCoord3D ax x y z = ax.fromSiteMSet (mkPureCoord3D x y z)

public export
unitAxesFromAtoms :
  Ord k =>
  (PureMultiset -> k) ->
  (k -> k -> k) ->
  k ->
  Box BoxInt PureMultiset ->
  Box BoxInt k
unitAxesFromAtoms stepFn subFn zeroK =
  foldBox (\axKey, _, acc =>
             let d = stepFn axKey
             in addAtKeyBox (subFn zeroK d) (MkBoxInt 1) (addAtKeyBox d (MkBoxInt 1) acc))
          BoxLeaf

public export
collectSiteAxisAtoms : PureMultiset -> Box BoxInt PureMultiset -> Box BoxInt PureMultiset
collectSiteAxisAtoms (MkHMSet b) acc0 =
  supportBox (acc0 <+> filterBox isAxisAtom b)

||| Unions `ax.baseAxes` with all emergent positive axis atoms `{ [] : i }` present in `pol`.
public export
activeAxisAtomsOf : AxisBasis k -> PolarityMaxel k -> Box BoxInt PureMultiset
activeAxisAtomsOf ax pol =
  if not ax.allowEmergentAxes
    then ax.baseAxes
    else foldStoredMaxel
           (\a, b, _, acc =>
              collectSiteAxisAtoms (ax.toSiteMSet b)
                (collectSiteAxisAtoms (ax.toSiteMSet a) acc))
           ax.baseAxes pol

public export
activeUnitAxesOf : Ord k => AxisBasis k -> PolarityMaxel k -> Box BoxInt k
activeUnitAxesOf ax pol =
  if not ax.allowEmergentAxes
    then ax.unitAxes
    else
      let atoms = activeAxisAtomsOf ax pol
      in if atoms == ax.baseAxes
           then ax.unitAxes
           else unitAxesFromAtoms ax.axisStep ax.shiftSub (ax.fromSiteMSet emptyHMSet) atoms

||| Builds a fixed-dimension `AxisBasis k` over any `GroupCoord k`.
public export
mkGroupAxisBasis :
  GroupCoord k =>
  (axes     : Box BoxInt PureMultiset) ->
  (stepFn   : PureMultiset -> k) ->
  (oddFn    : PureMultiset -> k -> Bool) ->
  (toMSet   : k -> PureMultiset) ->
  (fromMSet : PureMultiset -> k) ->
  AxisBasis k
mkGroupAxisBasis axes stepFn oddFn toMSet fromMSet =
  let subFn = \a, b => combine a (inverse b)
  in MkAxisBasis
       axes
       False
       stepFn
       oddFn
       combine
       subFn
       toMSet
       fromMSet
       (unitAxesFromAtoms stepFn subFn origin axes)

public export
baseAxes1D : Box BoxInt PureMultiset
baseAxes1D = singletonBox axisX (MkBoxInt 1)

public export
coord1Basis : AxisBasis SignedCoord
coord1Basis =
  mkGroupAxisBasis
    baseAxes1D
    (\_ => PosZ 0)
    (\_, x => isOddSigned x)
    (\x => singletonHMSet axisX (signedToBoxInt x))
    (\m => boxIntToSigned (lookupKeyHMSet axisX m))

public export
baseAxes2D : Box BoxInt PureMultiset
baseAxes2D = setBox axisY (MkBoxInt 1) baseAxes1D

public export
coord2Step : PureMultiset -> Coord2
coord2Step axKey = if axKey == axisX then (PosZ 0, ZeroZ) else (ZeroZ, PosZ 0)

public export
coord2Basis : AxisBasis Coord2
coord2Basis =
  mkGroupAxisBasis
    baseAxes2D
    coord2Step
    (\axKey, (x, y) => if axKey == axisX then isOddSigned x else isOddSigned y)
    (\(x, y) => MkHMSet (addAtKeyBox axisY (signedToBoxInt y) (singletonBox axisX (signedToBoxInt x))))
    (\m => (boxIntToSigned (lookupKeyHMSet axisX m), boxIntToSigned (lookupKeyHMSet axisY m)))

public export
baseAxes3D : Box BoxInt PureMultiset
baseAxes3D = setBox axisZ (MkBoxInt 1) baseAxes2D

public export
coord3Step : PureMultiset -> Coord3
coord3Step axKey =
  if axKey == axisX then (PosZ 0, (ZeroZ, ZeroZ))
  else if axKey == axisY then (ZeroZ, (PosZ 0, ZeroZ))
  else (ZeroZ, (ZeroZ, PosZ 0))

public export
coord3Basis : AxisBasis Coord3
coord3Basis =
  mkGroupAxisBasis
    baseAxes3D
    coord3Step
    (\axKey, (x, (y, z)) =>
       if axKey == axisX then isOddSigned x
       else if axKey == axisY then isOddSigned y
       else isOddSigned z)
    (\(x, (y, z)) =>
       MkHMSet $ addAtKeyBox axisZ (signedToBoxInt z)
               $ addAtKeyBox axisY (signedToBoxInt y)
               $ singletonBox axisX (signedToBoxInt x))
    (\m => (boxIntToSigned (lookupKeyHMSet axisX m),
           (boxIntToSigned (lookupKeyHMSet axisY m),
            boxIntToSigned (lookupKeyHMSet axisZ m))))

public export
buildPureAxesBox : Nat -> Integer -> Box BoxInt PureMultiset -> Box BoxInt PureMultiset
buildPureAxesBox Z       _   acc = acc
buildPureAxesBox (S rem) idx acc =
  buildPureAxesBox rem (idx + 1) (setBox (scalarKeyHMSet idx) (MkBoxInt 1) acc)

public export
pureStepOfAtom : PureMultiset -> PureMultiset
pureStepOfAtom = wrapBox

public export
pureMSetBasisND : Nat -> AxisBasis PureMultiset
pureMSetBasisND dim =
  let axesBox = buildPureAxesBox dim 1 BoxLeaf
  in MkAxisBasis
       axesBox
       True
       pureStepOfAtom
       (\axKey, pos => isOddBox (lookupKeyHMSet axKey pos))
       addHMSet
       subHMSet
       id
       projectToSiteMSet
       (unitAxesFromAtoms pureStepOfAtom subHMSet emptyHMSet axesBox)

public export
pureMSetBasis : AxisBasis PureMultiset
pureMSetBasis = pureMSetBasisND 2

--------------------------------------------------------------------------------
-- 3. DYNAMICS PARAMETERS, EVOLUTION STATE & DERIVED QUADRANCE REDUCTIONS
--------------------------------------------------------------------------------

public export
canonLagDiv : Integer
canonLagDiv = 6000000

public export
canonDecayNum : Integer
canonDecayNum = 7

public export
canonDecayDen : Integer
canonDecayDen = 32

public export
canonLinkCoup : Integer
canonLinkCoup = 1

public export
canonPacedSubTicks : Nat
canonPacedSubTicks = 4

public export
data StepMode
  = ModeLinear
  | ModeFactor Nat Nat

public export
ModeSpread : StepMode
ModeSpread = ModeFactor 1 canonPacedSubTicks

public export
ModeBalanced : StepMode
ModeBalanced = ModeFactor 2 2

public export
ModePaced : StepMode
ModePaced = ModeFactor canonPacedSubTicks 1

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
  MkDynamicsParams mode 7 canonLagDiv canonDecayNum canonDecayDen canonLinkCoup

||| Blind local evolution state over any discrete coordinate basis `k`:
||| - `polarityMaxel` : half-stored diagonal site polarity + antisymmetric edge flux (`DiagAntisymForm`)
||| - `loadMaxel`     : causal 1-hop retarded interaction load (`SymForm`) propagating at `c = 1`
||| - `throttleMaxel` : sparse integer Bresenham pacing accumulator (`SymForm`, pruned at `0`)
public export
record EvolutionState (k : Type) where
  constructor MkEvolutionState
  polarityMaxel : PolarityMaxel k
  loadMaxel     : QuadranceMaxel k
  throttleMaxel : QuadranceMaxel k

public export
emptyEvolutionState : EvolutionState k
emptyEvolutionState = MkEvolutionState emptyMaxel emptyMaxel emptyMaxel

public export
addEvolutionState : Ord k => EvolutionState k -> EvolutionState k -> EvolutionState k
addEvolutionState a b =
  MkEvolutionState
    (a.polarityMaxel <+> b.polarityMaxel)
    (a.loadMaxel <+> b.loadMaxel)
    (a.throttleMaxel <+> b.throttleMaxel)

public export
Ord k => Semigroup (EvolutionState k) where
  (<+>) = addEvolutionState

public export
Ord k => Monoid (EvolutionState k) where
  neutral = emptyEvolutionState

||| Canonical `QuadranceMaxel k` (`SymForm`) of `pol : PolarityMaxel k`:
||| diagonal `(a, a)` holds `2 * p(a)^2` and off-diagonal `(a, b)` (`a < b`) holds `u_{ab}^2`.
public export
quadranceOf : Ord k => PolarityMaxel k -> QuadranceMaxel k
quadranceOf pol =
  let pSq = pol .*. pol
  in pSq <+> diagEmbedMaxel (diagBox pSq)

||| Total quadrance `2 * sum p(a)^2 + sum_{a < b} u_{ab}^2` via `sumStoredMaxel` of `quadranceOf pol`.
public export
polarityQuadranceOf : Ord k => PolarityMaxel k -> Integer
polarityQuadranceOf pol = unwrapBox (sumStoredMaxel (quadranceOf pol))

public export
stateQuadrance : Ord k => EvolutionState k -> Integer
stateQuadrance st = polarityQuadranceOf st.polarityMaxel

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
-- 4. BALANCED ZERO-SUM EXCITATIONS & BOUND DIPOLES (2D, 3D & ND)
--------------------------------------------------------------------------------

public export
seedDipoleSites : Ord k => (pPos, pNeg : k) -> (amp : BoxInt) -> EvolutionState k
seedDipoleSites pPos pNeg amp =
  let w = addAtMaxelEdge pNeg pNeg (negate amp) (singletonMaxelEdge pPos pPos amp)
  in MkEvolutionState w emptyMaxel emptyMaxel

||| Seeds an oscillating bound polarity dipole (`+amp` and `-amp` across adjacent coordinates).
public export
seedBoundDipole : Ord k => AxisBasis k -> (x, yPos, yNeg : Integer) -> (amp : BoxInt) -> EvolutionState k
seedBoundDipole ax x yPos yNeg amp =
  seedDipoleSites (mkCoord2D ax x yPos) (mkCoord2D ax x yNeg) amp

public export
transverseEnv4 : Ord k => (Integer -> k) -> (t0 : Integer) -> (halfA, fullA : BoxInt) -> Box BoxInt k
transverseEnv4 mkAxisCoord t0 halfA fullA =
  addAtKeyBox (mkAxisCoord (t0 - 1)) halfA $
  addAtKeyBox (mkAxisCoord t0)       fullA $
  addAtKeyBox (mkAxisCoord (t0 + 1)) fullA $
  singletonBox (mkAxisCoord (t0 + 2)) halfA

||| Balanced zero-sum 4-row directed pulse propagating along `+X` across any transverse coordinate generator.
public export
seedDirectedPulse :
  Ord k =>
  AxisBasis k ->
  (mkTransCoord : Integer -> k) ->
  (x0, t0 : Integer) ->
  (amp : BoxInt) ->
  EvolutionState k
seedDirectedPulse ax mkTransCoord x0 t0 amp =
  let halfA  = tdiv2Box amp
      tEnv   = transverseEnv4 mkTransCoord t0 halfA amp
      e1     = mkCoord2D ax (x0 - 2) 0
      e2     = mkCoord2D ax (x0 - 1) 0
      e3     = mkCoord2D ax x0 0
      e4     = mkCoord2D ax (x0 + 1) 0
      e5     = mkCoord2D ax (x0 + 2) 0
      rowPol = setMaxelEdge e2 e2 (MkBoxInt (-1)) $
               setMaxelEdge e4 e4 (MkBoxInt 1)    $
               setMaxelEdge e1 e2 (MkBoxInt (-2)) $
               setMaxelEdge e2 e3 (MkBoxInt (-2)) $
               setMaxelEdge e3 e4 (MkBoxInt 2)    $
               singletonMaxelEdge e4 e5 (MkBoxInt 2)
  in MkEvolutionState (shiftConvolveMaxel ax.shiftAdd rowPol tEnv) emptyMaxel emptyMaxel

public export
seedExcitationAt : Ord k => AxisBasis k -> (x0, y0 : Integer) -> (amp : BoxInt) -> EvolutionState k
seedExcitationAt ax = seedDirectedPulse ax (mkCoord2D ax 0)

public export
seedExcitation : Ord k => AxisBasis k -> (x0 : Integer) -> (amp : BoxInt) -> EvolutionState k
seedExcitation ax x0 amp = seedExcitationAt ax x0 0 amp

||| Seeds a balanced zero-sum antisymmetric directed-edge flux link `(x1, y1) -> (x2, y2)` with weight `u`.
public export
seedEdgeFlux : Ord k => AxisBasis k -> (x1, y1, x2, y2 : Integer) -> (u : BoxInt) -> EvolutionState k
seedEdgeFlux ax x1 y1 x2 y2 u =
  MkEvolutionState (singletonMaxelEdge (mkCoord2D ax x1 y1) (mkCoord2D ax x2 y2) u) emptyMaxel emptyMaxel

||| Polymorphic 3D bound polarity dipole displaced along Z over any `AxisBasis k` (`Coord3` or `PureMultiset`).
public export
seedBoundDipole3DZ : Ord k => AxisBasis k -> (x, y, zPos, zNeg : Integer) -> (amp : BoxInt) -> EvolutionState k
seedBoundDipole3DZ ax x y zPos zNeg amp =
  seedDipoleSites (mkCoord3D ax x y zPos) (mkCoord3D ax x y zNeg) amp

||| Polymorphic 3D localized excitation propagating along `+X` at slice `y = y0` with a 4-layer transverse Z envelope.
public export
seedExcitation3DZ : Ord k => AxisBasis k -> (x0, y0, z0 : Integer) -> (amp : BoxInt) -> EvolutionState k
seedExcitation3DZ ax x0 y0 z0 amp =
  seedDirectedPulse ax (mkCoord3D ax 0 y0) x0 z0 amp

--------------------------------------------------------------------------------
-- 5. CAUSAL 1-HOP INTERACTION LOAD & ENDOGENOUS BRESENHAM THROTTLING
--------------------------------------------------------------------------------

||| Causal 1-hop symmetric `QuadranceMaxel k` source derived directly from `qM = quadranceOf pol`.
public export
activeQuadranceSource :
  Ord k =>
  Bool ->
  (linkCoup : Integer) ->
  (pol : PolarityMaxel k) ->
  QuadranceMaxel k
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
                    else scaleMaxel (MkBoxInt linkCoup) fluxSq
  in siteSrc <+> linkSrc

||| Causal 1-hop retarded interaction-load step across arbitrary-dimension `unitSt` (`c = 1`, `SymForm`).
public export
stepCausalLoadMaxel :
  Ord k =>
  AxisBasis k ->
  (unitSt : Box BoxInt k) ->
  (lagDiv, decayNum, decayDen : Integer) ->
  (actSrcM : QuadranceMaxel k) ->
  (oldLoad : QuadranceMaxel k) ->
  QuadranceMaxel k
stepCausalLoadMaxel ax unitSt lagDiv decayNum decayDen actSrcM oldLoad =
  if lagDiv <= 0
    then emptyMaxel
    else
      let rawMin  = divIntegerPos lagDiv 16
          minCut  = if rawMin < 1 then 1 else rawMin
          decayed = if isEmptyMaxel oldLoad || decayDen <= 0
                      then emptyMaxel
                      else scaleDivPruneMaxel decayDen minCut
                             (scaleMaxel (MkBoxInt decayNum)
                                (shiftConvolveMaxel ax.shiftAdd oldLoad unitSt))
      in decayed <+> pruneMinMaxel minCut actSrcM

||| Canonical start vertex `s` when `(a, b)` spans an undirected step along `stepDir`.
public export
canonLinkStart : Ord k => AxisBasis k -> k -> k -> k -> Maybe k
canonLinkStart ax stepDir a b =
  if b == ax.shiftAdd a stepDir then Just a
  else if a == ax.shiftAdd b stepDir then Just b
  else Nothing

||| Collects strictly active canonical links `(s, s + stepDir)` touching non-zero sites or edges of `pol`.
public export
collectAxisLinks : Ord k => AxisBasis k -> k -> PolarityMaxel k -> Box BoxInt k
collectAxisLinks ax stepDir pol =
  foldStoredMaxel
    (\a, b, _, acc =>
       if a == b
         then setBox a (MkBoxInt 1) (setBox (ax.shiftSub a stepDir) (MkBoxInt 1) acc)
         else case canonLinkStart ax stepDir a b of
                Just s  => setBox s (MkBoxInt 1) acc
                Nothing => acc)
    BoxLeaf
    pol

public export
applyLinkExchangePow : Ord k => (y : Nat) -> (posA, posB : k) -> (m, pA, pB, uOld : BoxInt) -> PolarityMaxel k -> PolarityMaxel k
applyLinkExchangePow Z       _    _    _ _  _  _    pol = pol
applyLinkExchangePow y@(S _) posA posB m pA pB uOld pol =
  let res = exchangeQuadraticPow y m pA pB uOld
      w1  = if res.valA /= pA then setMaxelEdge posA posA res.valA pol else pol
      w2  = if res.valB /= pB then setMaxelEdge posB posB res.valB w1  else w1
  in if res.valU /= uOld then setMaxelEdge posA posB res.valU w2 else w2

public export
linkLoadSum : Ord k => QuadranceMaxel k -> k -> k -> BoxInt
linkLoadSum loadM posA posB =
  lookupMaxel posA posA loadM + lookupMaxel posB posB loadM + lookupMaxel posA posB loadM

public export
sweepAxisPass :
  Ord k =>
  AxisBasis k ->
  (stepDir : k) ->
  (wantOdd : Bool) ->
  (isOddFn : k -> Bool) ->
  (linksBox : Box BoxInt k) ->
  (getPol : acc -> PolarityMaxel k) ->
  (onLink : k -> k -> BoxInt -> BoxInt -> BoxInt -> acc -> acc) ->
  acc ->
  acc
sweepAxisPass ax stepDir wantOdd isOddFn linksBox getPol onLink initAcc =
  foldBox (\posA, _, acc =>
             if isOddFn posA /= wantOdd
               then acc
               else
                 let posB = ax.shiftAdd posA stepDir
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
  Ord k =>
  AxisBasis k ->
  Box BoxInt PureMultiset ->
  (getPol : acc -> PolarityMaxel k) ->
  (onLink : k -> k -> BoxInt -> BoxInt -> BoxInt -> acc -> acc) ->
  acc ->
  acc
sweepCheckerboard ax axesBox getPol onLink acc0 =
  foldBox (\axKey, _, acc =>
             let stepDir = ax.axisStep axKey
                 isOddFn = ax.isOddAxis axKey
                 links   = collectAxisLinks ax stepDir (getPol acc)
                 accE    = sweepAxisPass ax stepDir False isOddFn links getPol onLink acc
             in sweepAxisPass ax stepDir True isOddFn links getPol onLink accE)
          acc0
          axesBox

public export
record PacedPassAcc (k : Type) where
  constructor MkPacedPassAcc
  ppPolarity : PolarityMaxel k
  ppThrottle : QuadranceMaxel k
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
  Ord k =>
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
          paceBudget = if lagDiv > 0 && m0 > 0 then m0 * lagDiv else 0
          axesBox    = activeAxisAtomsOf ax st.polarityMaxel
          unitSt     = activeUnitAxesOf ax st.polarityMaxel
          actSrc0    = activeQuadranceSource (lagDiv > 0) linkCoup st.polarityMaxel
          newLoad    = stepCausalLoadMaxel ax unitSt lagDiv decayNum decayDen actSrc0 st.loadMaxel
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
                                pol1  = applyLinkExchangePow yCnt posA posB (MkBoxInt mSub) pA pB uOld a.ppPolarity
                            in MkPacedPassAcc pol1 thr1 (a.ppYields + yCnt) (a.ppSkips + sCnt))
                         acc
            in runPasses rem acc1
          pFin       = runPasses outerPasses (MkPacedPassAcc st.polarityMaxel st.throttleMaxel 0 0)
      in (MkEvolutionState pFin.ppPolarity newLoad pFin.ppThrottle, (pFin.ppYields, pFin.ppSkips))

||| Evaluates one blind evolution step under explicit `DynamicsParams`.
public export
stepDynamicsWith :
  Ord k =>
  AxisBasis k ->
  DynamicsParams ->
  EvolutionState k ->
  (EvolutionState k, (Nat, Nat))
stepDynamicsWith ax p st =
  case p.dpMode of
    ModeLinear       => stepDynamicsCore ax 1  1  0          p.dpDecayNum p.dpDecayDen 0            p.dpGenM0 st
    ModeFactor oP iT => stepDynamicsCore ax oP iT p.dpLagDiv p.dpDecayNum p.dpDecayDen p.dpLinkCoup p.dpGenM0 st

||| Single streaming step over `EvolutionState k` charging `GohFuel` only on `StreamYield`.
public export
stepDynamicsStreamWith :
  Ord k =>
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

||| Streams `st0` via `freezeStateStreamWith` under explicit `DynamicsParams` and `(yieldFuel : GohFuel cap, stepBudget : Nat)`.
public export
freezeDynamicsStreamWith :
  {0 cap     : Nat} ->
  Ord k =>
  AxisBasis k ->
  DynamicsParams ->
  (g          : Nat) ->
  (yieldFuel  : GohFuel cap) ->
  (stepBudget : Nat) ->
  EvolutionState k ->
  (SolidifiedStream (StaticTime (- cast g) (cast cap)) cap (EvolutionState k), Nat)
freezeDynamicsStreamWith ax params g yFuel sBudget st0 =
  freezeStateStreamWith g yFuel sBudget (stepDynamicsStreamWith ax params) st0

||| Injects any peeled `Configuration` relic key `k` (directed edge `mkEdgeKey a b` or site key `s`)
||| directly over `AxisBasis k` with flux weight `amp` — preserving negative coordinates and 3D/ND axes
||| with zero `(Nat, Nat, Nat)` tuple conversion.
public export
injectRelicBond : Ord k => AxisBasis k -> EvolutionState k -> Configuration -> BoxInt -> EvolutionState k
injectRelicBond ax u k amp =
  let (posA, posB) =
        case unpackEdgeKey k of
          Just (a, b) => (ax.fromSiteMSet a, ax.fromSiteMSet b)
          Nothing     =>
            let s = ax.fromSiteMSet (projectToSiteMSet k)
            in (s, ax.shiftAdd s (ax.axisStep axisX))
  in u <+> MkEvolutionState (singletonMaxelEdge posA posB amp) emptyMaxel emptyMaxel

||| Coupled two-multiset boundary flow parameterized by `DynamicsParams`:
||| external reservoir `eSrc : Configuration` peels 1 bond quantum (`qAmp`, quadrance `qAmp^2`) per tick
||| into `u : EvolutionState k` via `viewAsAntiBox eSrc`, decoupling into closed evolution once `eSrc == []`.
public export
stepCoupledSourceFlow :
  Ord k =>
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
||| across any `seam : PolarityMaxel k` boundary mask (`maskByMaxel`, zero global oracle).
public export
stepCoupledUniversePair :
  Ord k =>
  AxisBasis k ->
  DynamicsParams ->
  (seam : PolarityMaxel k) ->
  (qAmp : BoxInt) ->
  (EvolutionState k, EvolutionState k) ->
  (StreamStep (EvolutionState k, EvolutionState k), Nat, Nat)
stepCoupledUniversePair ax params seam qAmp (uA, uB) =
  let clampQ   = \w =>
        if w >= qAmp then qAmp
        else if w <= negate qAmp then negate qAmp
        else tdiv2Box w
      deltaPol = mapPruneMaxel clampQ (maskByMaxel (subMaxel uA.polarityMaxel uB.polarityMaxel) seam)
      deltaSt  = MkEvolutionState deltaPol emptyMaxel emptyMaxel
      negSt    = MkEvolutionState (negateMaxel deltaPol) emptyMaxel emptyMaxel
      (nA, (yA, sA)) = stepDynamicsWith ax params (uA <+> negSt)
      (nB, (yB, sB)) = stepDynamicsWith ax params (uB <+> deltaSt)
  in if yA + yB == 0 && sA + sB == 0
       then (StreamDone, 0, 0)
       else (StreamYield (nA, nB), max 1 (yA + yB), sA + sB)

--------------------------------------------------------------------------------
-- 6. COMPILE-TIME QTT 0 ALGEBRAIC INVARIANTS
--------------------------------------------------------------------------------

public export
0 prfAntisymSingleEdge :
  (let e = FinScBox.Box.singletonMaxelEdge {form = AntisymForm} (ZeroZ, ZeroZ) (PosZ 0, ZeroZ) (MkBoxInt 12)
   in (FinScBox.Box.maxelNodeCount e == 1) &&
      (FinScBox.Box.traceMaxel e == MkBoxInt 0) &&
      (FinScBox.Box.lookupMaxel (PosZ 0, ZeroZ) (ZeroZ, ZeroZ) e == MkBoxInt (-12))) = True
prfAntisymSingleEdge = Refl

public export
0 prfBoundDipoleZeroNet :
  FinScDynamics.Evolution.statePolarityNet
    (FinScDynamics.Evolution.seedBoundDipole FinScDynamics.Evolution.coord2Basis 0 0 1 10) = 0
prfBoundDipoleZeroNet = Refl

public export
0 prfQuadranceMaxelTotalMass :
  (let dp = FinScDynamics.Evolution.seedBoundDipole FinScDynamics.Evolution.coord2Basis 0 0 1 10
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
  FinScDynamics.Evolution.mkPureCoord3D (-8) 7 (-3) + FinScDynamics.Evolution.stepX
  = FinScDynamics.Evolution.mkPureCoord3D (-7) 7 (-3)
prfPureStepShift = Refl

public export
0 prfEdgeKeyRoundTrip :
  (let pA = mkPureCoord3D (-2) 5 1
       pB = mkPureCoord3D (-1) 5 1
       k  = mkEdgeKey pA pB
   in case unpackEdgeKey k of
        Just (a, b) => (a == pA) && (b == pB)
        Nothing     => False) = True
prfEdgeKeyRoundTrip = Refl
