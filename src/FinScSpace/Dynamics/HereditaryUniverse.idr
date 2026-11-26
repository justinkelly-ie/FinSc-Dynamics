module FinScSpace.Dynamics.HereditaryUniverse

import Control.App
import FinScBox.BoxInt
import FinScBox.Interfaces
import FinScBox.Box
import FinScBox.HereditaryMSet
import FinScBox.Lenses
import FinScBox.BlackRedZoom
import FinScSpace.Dynamics.Evolution

%default total

--------------------------------------------------------------------------------
-- 1. DISJOINT STRUCTURAL SHAPES INSIDE ONE `Configuration` (`PureMultiset`)
--    Five mutually disjoint structural shapes with ZERO synthetic integer tags:
--      1. Active D-Dim Vertex       : positive scalar axis atoms `{ [] : i }` (`isSiteKey`)
--      2. Active Directed Edge      : `{ wrapBox posA : +1, wrapBox posB : -1 }` (`mkEdgeKey`)
--      3. Causal Load Dipole        : `wrapBox (wrapBox loadM)` (`mkLoadKey`)
--      4. Throttle Balance Dipole   : `wrapBox { thrM : -1 }` (`mkThrottleKey`)
--      5. Localized Sub-Config      : `{ wrapBox pos : +1, { pay : -2 } : +2 }` (`mkLocalizedKey`)
--------------------------------------------------------------------------------

||| Pure causal interaction-load key `wrapBox (wrapBox loadM)` inside `Configuration`.
public export
mkLoadKey : Configuration -> Configuration
mkLoadKey loadM = wrapBox (wrapBox loadM)

||| Decoder for wrapped causal interaction-load keys `mkLoadKey loadM`.
public export
unpackLoadKey : Configuration -> Maybe Configuration
unpackLoadKey entry =
  if isSiteKey entry
    then Nothing
    else do
      inner <- extractWrapBox entry
      loadM <- extractWrapBox inner
      if loadM == emptyHMSet then Nothing else Just loadM

||| Pure local pacing-throttle key `wrapBox { thrM : -1 }` inside `Configuration`.
public export
mkThrottleKey : Configuration -> Configuration
mkThrottleKey thrM = wrapBox (singletonHMSet thrM (MkBoxInt (-1)))

||| Decoder for wrapped local pacing-throttle keys `mkThrottleKey thrM`.
public export
unpackThrottleKey : Configuration -> Maybe Configuration
unpackThrottleKey entry =
  if isSiteKey entry
    then Nothing
    else do
      inner <- extractWrapBox entry
      thrM  <- extractSignedWrap (MkBoxInt (-1)) inner
      if thrM == emptyHMSet then Nothing else Just thrM

||| Pure localized sub-configuration key `{ wrapBox pos : +1, { payload : -2 } : +2 }` over any `Configuration` site `pos`.
public export
mkLocalizedKey : (pos, payload : Configuration) -> Configuration
mkLocalizedKey pos payload =
  let kPos = wrapBox pos
      kPay = singletonHMSet payload (MkBoxInt (-2))
  in MkHMSet $ setBox kPay (MkBoxInt 2) (singletonBox kPos (MkBoxInt 1))

||| Decoder for pure localized sub-configuration keys `mkLocalizedKey`.
public export
unpackLocalizedKey : Configuration -> Maybe (Configuration, Configuration)
unpackLocalizedKey entry@(MkHMSet b) =
  if isSiteKey entry || treeSizeNonZero b /= 2
    then Nothing
    else do
      kPos <- extractUniqueSlot (MkBoxInt 1) b
      kPay <- extractUniqueSlot (MkBoxInt 2) b
      p    <- extractWrapBox kPos
      pay  <- extractSignedWrap (MkBoxInt (-2)) kPay
      Just (p, pay)

||| Extracts a localized sub-configuration payload at native site key `targetPos : Configuration`
||| (supporting negative coordinates and arbitrary dimensions with zero tuple conversion).
public export
lookupLocalizedAt : (targetPos : Configuration) -> Configuration -> Configuration
lookupLocalizedAt targetPos (MkHMSet b) =
  fromMaybe emptyHMSet $
    findBox (\entry, _ =>
               case unpackLocalizedKey entry of
                 Just (posM, pay) => if posM == targetPos then Just pay else Nothing
                 Nothing          => Nothing)
            b

--------------------------------------------------------------------------------
-- 2. ZERO-TAG ZERO-COPY HEREDITARY ROOT CODEC (`EvolutionState <-> Configuration`)
--------------------------------------------------------------------------------

public export
addBalancedUnitDipole : (posK, negK : Configuration) -> Box BoxInt Configuration -> Box BoxInt Configuration
addBalancedUnitDipole posK negK =
  addAtKeyBox negK (MkBoxInt (-1)) . addAtKeyBox posK (MkBoxInt 1)

public export
hasBalancedPartner : (oppK : Configuration) -> (mult : BoxInt) -> Box BoxInt Configuration -> Bool
hasBalancedPartner oppK mult rootBox =
  let expOpp = negWeight mult
  in not (boxIsZero expOpp) && lookupBox oppK rootBox == expOpp

||| Packs active polarity sites (`a == b -> a`) and balanced directed-edge pairs (`mkEdgeKey a b : +w`, `mkEdgeKey b a : -w`).
public export
packPolarityBox :
  Box BoxInt Configuration ->
  Maxel BoxInt PureMultiset PureMultiset DiagAntisymForm ->
  Box BoxInt Configuration
packPolarityBox base pol =
  foldStoredMaxel
    (\posA, posB, w, acc =>
       if posA == posB
         then addAtKeyBox posA w acc
         else addAtKeyBox (mkEdgeKey posB posA) (negWeight w) $
              addAtKeyBox (mkEdgeKey posA posB) w acc)
    base pol

public export
packSymMaxelToHMSet : Maxel BoxInt PureMultiset PureMultiset SymForm -> Configuration
packSymMaxelToHMSet symM =
  MkHMSet $ foldStoredMaxel
              (\posA, posB, w, acc =>
                 if posA == posB
                   then addAtKeyBox posA w acc
                   else addAtKeyBox (mkEdgeKey posA posB) w acc)
              BoxLeaf symM

public export
unpackHMSetToSymMaxel : Configuration -> Maxel BoxInt PureMultiset PureMultiset SymForm
unpackHMSetToSymMaxel (MkHMSet b) =
  foldBox (\entry, mult, acc =>
             if isSiteKey entry
               then addAtMaxelEdge entry entry mult acc
               else case unpackEdgeKey entry of
                      Just (a, b) => addAtMaxelEdge a b mult acc
                      Nothing     => acc)
          emptyMaxel b

public export
packSymDipole :
  (Configuration -> Configuration) ->
  Maxel BoxInt PureMultiset PureMultiset SymForm ->
  Box BoxInt Configuration ->
  Box BoxInt Configuration
packSymDipole mkKey maxel acc =
  let m = packSymMaxelToHMSet maxel
  in if m == emptyHMSet
       then acc
       else addBalancedUnitDipole (mkKey m) (mkKey (-m)) acc

public export
hasSignedUnitPartner : (oppK : Configuration) -> (mult : BoxInt) -> Box BoxInt Configuration -> Bool
hasSignedUnitPartner oppK mult rootBox =
  (mult == MkBoxInt 1 || mult == MkBoxInt (-1)) &&
  hasBalancedPartner oppK mult rootBox

||| Packs `EvolutionState PureMultiset` cleanly into ONE zero-sum `Configuration` root
||| with ZERO synthetic tags and `O(1)` zero-copy sealing for load and throttle dipoles.
public export
packEvolutionStateToRoot : Box BoxInt Configuration -> EvolutionState PureMultiset -> Configuration
packEvolutionStateToRoot keptBox st =
  let bAct = packPolarityBox keptBox st.polarityMaxel
      bLd  = packSymDipole mkLoadKey st.loadMaxel bAct
      bThr = packSymDipole mkThrottleKey st.throttleMaxel bLd
  in MkHMSet bThr

public export
record RootUnpackAcc where
  constructor MkRootUnpackAcc
  keptNonField : Box BoxInt Configuration
  stateData    : EvolutionState PureMultiset

public export
Eq RootUnpackAcc where
  a == b = a.keptNonField == b.keptNonField && a.stateData == b.stateData

public export
decodeRootEntry : Configuration -> BoxInt -> (Box BoxInt Configuration, EvolutionState PureMultiset)
decodeRootEntry entry mult =
  if isSiteKey entry
    then (BoxLeaf, MkEvolutionState (addAtMaxelEdge entry entry mult emptyMaxel) emptyMaxel emptyMaxel)
    else case unpackEdgeKey entry of
           Just (a, b) =>
             (BoxLeaf, if compare a b == LT
                         then MkEvolutionState (addAtMaxelEdge a b mult emptyMaxel) emptyMaxel emptyMaxel
                         else neutral)
           Nothing =>
             case unpackLoadKey entry of
               Just loadM =>
                 (BoxLeaf, if mult == MkBoxInt 1 then MkEvolutionState emptyMaxel (unpackHMSetToSymMaxel loadM) emptyMaxel else neutral)
               Nothing =>
                 case unpackThrottleKey entry of
                   Just thrM =>
                     (BoxLeaf, if mult == MkBoxInt 1 then MkEvolutionState emptyMaxel emptyMaxel (unpackHMSetToSymMaxel thrM) else neutral)
                   Nothing =>
                     (singletonBox entry mult, neutral)

||| Single-pass zero-copy decoder from `root : Configuration` to `EvolutionState PureMultiset` via `<+>`.
public export
unpackRootToEvolutionState : Configuration -> RootUnpackAcc
unpackRootToEvolutionState (MkHMSet rootBox) =
  foldBox (\entry, mult, acc =>
             let (kBox, stDelta) = decodeRootEntry entry mult
             in MkRootUnpackAcc (acc.keptNonField <+> kBox) (acc.stateData <+> stDelta))
          (MkRootUnpackAcc BoxLeaf neutral)
          rootBox

||| Verifies explicitly that every active edge pair, load dipole, and throttle dipole
||| inside `root` appears with its canonical opposing partner.
public export
verifyRootBalancedDipoles : Configuration -> Bool
verifyRootBalancedDipoles (MkHMSet rootBox) =
  allBox (\entry, mult =>
            isSiteKey entry ||
            case unpackEdgeKey entry of
              Just (a, b) => hasBalancedPartner (mkEdgeKey b a) mult rootBox
              Nothing =>
                case unpackLoadKey entry of
                  Just loadM => hasSignedUnitPartner (mkLoadKey (-loadM)) mult rootBox
                  Nothing =>
                    case unpackThrottleKey entry of
                      Just thrM => hasSignedUnitPartner (mkThrottleKey (-thrM)) mult rootBox
                      Nothing   => True)
         rootBox

||| Model B closed sweep dispatcher under explicit `DynamicsParams` and `minDim` base axes.
public export
stepHereditaryWithRoot : (minDim : Nat) -> DynamicsParams -> Configuration -> Configuration
stepHereditaryWithRoot minDim params root =
  let unp      = unpackRootToEvolutionState root
      (st1, _) = stepDynamicsWith (pureMSetBasis minDim) params unp.stateData
  in packEvolutionStateToRoot unp.keptNonField st1

public export
checkTagFreePackUnpackRoundTrip : Bool
checkTagFreePackUnpackRoundTrip =
  let actDp = seedBoundDipole (pureMSetBasis 3) [2, 1, 3] [2, 1, 4] 3
      p0    = mkPureCoord [0, 0, 0]
      p1    = mkPureCoord [1, 0, 1]
      edgeF = singletonMaxelEdge {form = DiagAntisymForm} p1 p0 (MkBoxInt 5)
      loadB = diagEmbedMaxel (singletonBox p0 (MkBoxInt 16)) <+> singletonMaxelEdge p1 p0 (MkBoxInt 25)
      thrB  = singletonMaxelEdge p0 p1 (MkBoxInt 11) <+>
              singletonMaxelEdge p0 (mkPureCoord [0, 1, 1]) (MkBoxInt (-23))
      st0   = MkEvolutionState (actDp.polarityMaxel <+> edgeF) loadB thrB
      root0 = packEvolutionStateToRoot BoxLeaf st0
      st1   = (unpackRootToEvolutionState root0).stateData
  in (unwrapBox (sumHMSet root0) == 0) &&
     verifyRootBalancedDipoles root0 &&
     isSymMaxel st1.loadMaxel &&
     (treeSizeNonZero (activeAxisAtomsOf (pureMSetBasis 2) st1.polarityMaxel) == 3) &&
     (treeSizeNonZero (activeUnitAxesOf (pureMSetBasis 2) st1.polarityMaxel) == 6) &&
     (st1.polarityMaxel == st0.polarityMaxel) &&
     (st1.loadMaxel == st0.loadMaxel) &&
     (st1.throttleMaxel == st0.throttleMaxel)

--------------------------------------------------------------------------------
-- 3. MODEL B: CLOSED OPAQUE 0D `Configuration` COMPUTE (`App1`, `NoThrow`)
--------------------------------------------------------------------------------

export
data HereditaryBlackBox : Type where
  MkHereditaryBox : (root : Configuration) -> HereditaryBlackBox

||| Boots Model B cleanly from the 0D vacuum root `[]`.
export
bootHereditary0D : App1 e HereditaryBlackBox
bootHereditary0D = App1.pure1 (MkHereditaryBox emptyHMSet)

||| Splits a balanced `+1` and `-1` subsystem pair carrying `payload` at native `Configuration` sites `posA` and `posB`.
export
splitHereditaryFromVacuum :
  (posA, posB : Configuration) ->
  (payload    : Configuration) ->
  (1 u        : HereditaryBlackBox) ->
  App1 e HereditaryBlackBox
splitHereditaryFromVacuum posA posB payload (MkHereditaryBox root) =
  let entryA = wrapBox (mkLocalizedKey posA payload)
      entryB = singletonHMSet (mkLocalizedKey posB payload) (MkBoxInt (-1))
  in App1.pure1 (MkHereditaryBox (root <+> entryA <+> entryB))

||| Superposes an arbitrary balanced zero-sum `EvolutionState PureMultiset` directly into `root : Configuration`.
export
injectHereditaryState :
  EvolutionState PureMultiset ->
  (1 u : HereditaryBlackBox) ->
  App1 e HereditaryBlackBox
injectHereditaryState delta (MkHereditaryBox root) =
  App1.pure1 (MkHereditaryBox (root <+> packEvolutionStateToRoot BoxLeaf delta))

||| Blind local evolution step directly inside `root : Configuration` under explicit `DynamicsParams` and `minDim`.
export
stepHereditaryWith :
  (minDim : Nat) ->
  DynamicsParams ->
  (1 u : HereditaryBlackBox) ->
  App1 e HereditaryBlackBox
stepHereditaryWith minDim params (MkHereditaryBox root) =
  App1.pure1 (MkHereditaryBox (stepHereditaryWithRoot minDim params root))

||| Universal non-perturbing external projection (`0 same : uOut = uIn`), observer-agnostic
||| across `FinSc-Lens` (`applyExternalLens lens`), projective frames, or raw readouts.
export
observeHereditaryPure :
  (Configuration -> out) ->
  (1 u : HereditaryBlackBox) ->
  App1 e (PureObservation u out)
observeHereditaryPure proj (MkHereditaryBox root) =
  let val = proj root
  in App1.pure1 (MkPureObs (MkHereditaryBox root) val Refl)

||| Consumes the linear `HereditaryBlackBox` once (`One -> Any`), returning the quenched final `Configuration`.
export
closeHereditary0D : (1 u : HereditaryBlackBox) -> App1 {u=Any} e Configuration
closeHereditary0D (MkHereditaryBox root) = App1.pure root

--------------------------------------------------------------------------------
-- 4. COMPILE-TIME QTT 0 DISJOINT-SHAPE & ZERO-SUM THEOREMS
--------------------------------------------------------------------------------

public export
0 prfFiveShapesDisjoint :
  (let sampleDipole = sampleUnitPairMSet
       site = mkPureCoord [-1, 2, -3]
       edge = mkEdgeKey emptyHMSet (wrapBox (axisAtom 2))
       load = mkLoadKey sampleDipole
       thr  = mkThrottleKey sampleDipole
       loc  = mkLocalizedKey (mkPureCoord [-5, 0, 2]) (scalarKeyHMSet 2)
   in isSiteKey site && isNothing (unpackEdgeKey site) && isNothing (unpackLoadKey site) && isNothing (unpackThrottleKey site) && isNothing (unpackLocalizedKey site) &&
      not (isSiteKey edge) && isNothing (unpackLoadKey edge) && isNothing (unpackThrottleKey edge) && isNothing (unpackLocalizedKey edge) &&
      not (isSiteKey load) && isNothing (unpackEdgeKey load) && isNothing (unpackThrottleKey load) && isNothing (unpackLocalizedKey load) &&
      not (isSiteKey thr)  && isNothing (unpackEdgeKey thr)  && isNothing (unpackLoadKey thr)  && isNothing (unpackLocalizedKey thr) &&
      not (isSiteKey loc)  && isNothing (unpackEdgeKey loc)  && isNothing (unpackLoadKey loc)  && isNothing (unpackThrottleKey loc)) = True
prfFiveShapesDisjoint = Refl

public export
0 prfTagFreeActiveVertexZeroSum :
  (let root0 = packEvolutionStateToRoot BoxLeaf (seedBoundDipole (pureMSetBasis 2) [0, 0] [0, 1] 10)
   in unwrapBox (sumHMSet root0) == 0) = True
prfTagFreeActiveVertexZeroSum = Refl
