module

public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.LocallyFinsupp
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.LocallyFiniteSum
public import stacks_project.Chap71.Lemma_71_10_7
public import stacks_project.Chap71.Lemma_71_10_10
public import stacks_project.Chap82.Definition_82_15_1_ClosedPushforward
public import stacks_project.Chap82.Definition_82_17_1_Cycle
public import stacks_project.Chap82.Lemma_82_19_1_Pullback

/-!
# Flat pullback of meromorphic-section divisors on algebraic spaces

In Situation 82.2.1, the flat pullback of the Weil divisor of a nonzero
meromorphic section of an invertible sheaf is the locally finite sum of the
multiplicity-weighted pushforwards of the induced divisors on the irreducible
components of the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open Function Set Topology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

export AlgebraicGeometry.AlgebraicSpace (flatPullback flatComponent isIntegral_flatComponent)

end Hom

namespace ClosedSubspace

export AlgebraicGeometry.AlgebraicSpace (componentMultiplicity)

end ClosedSubspace

namespace Hom

/-- The restriction of a good structure morphism to an irreducible component
remains quasi-separated. -/
instance instQuasiSeparated_flatComponent_structure {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] (η : genericPoints X) :
    QuasiSeparated ((flatComponent pX η).ι ≫ pX) :=
  sorry

/-- The restriction of a good structure morphism to an irreducible component
remains locally of finite type. -/
instance instLocallyOfFiniteType_flatComponent_structure {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (η : genericPoints X) :
    LocallyOfFiniteType ((flatComponent pX η).ι ≫ pX) :=
  sorry

/-- Pullbacks of meromorphic functions along the restriction of a flat morphism
to an irreducible component of the source are defined. -/
instance instPullbacksMeromorphicFunctionsDefined_flatComponent
    {S : Scheme.{u}} {B X Y : AlgebraicSpace S} [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX]
    (f : X ⟶ Y) [Flat f] [IsIntegral Y] (η : genericPoints X) :
    PullbacksMeromorphicFunctionsDefined ((flatComponent pX η).ι ≫ f) :=
  sorry

/-- The canonical irreducible component of `X` on a generic point is integral. -/
instance instIsIntegral_flatComponent {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [IsQuasiSeparated B] (pX : X ⟶ B) [QuasiSeparated pX]
    (η : genericPoints X) : IsIntegral (flatComponent pX η).X :=
  isIntegral_flatComponent pX η

/-- Pullback of an invertible module along the restriction of a morphism to an
irreducible component remains invertible. -/
instance instIsInvertibleObject_pullback_flatComponent {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX]
    (f : X ⟶ Y) (L : Y.Modules) [isInvertibleObject L] (η : genericPoints X) :
    isInvertibleObject ((Modules.pullback ((flatComponent pX η).ι ≫ f)).obj L) :=
  Modules.isInvertibleObject_pullback ((flatComponent pX η).ι ≫ f) L

/-- The pullback `s_i = f|_{X_i}^*(s)` of a meromorphic section of `L` to an
irreducible component of the source. -/
noncomputable def meromorphicSectionPullbackToFlatComponent {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r] [IsIntegral Y]
    (L : Y.Modules) [isInvertibleObject L]
    (s : meromorphicSections Y L) (η : genericPoints X) :
    meromorphicSections (flatComponent pX η).X
      ((Modules.pullback ((flatComponent pX η).ι ≫ f)).obj L) :=
  pullbackMeromorphicSections ((flatComponent pX η).ι ≫ f) L s

/-- The pulled-back meromorphic section on an irreducible component remains
regular. -/
theorem isRegularMeromorphicSection_flatComponent {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r] [IsIntegral Y]
    (L : Y.Modules) [isInvertibleObject L]
    (s : meromorphicSections Y L) (hs : IsRegularMeromorphicSection Y L s)
    (η : genericPoints X) :
    IsRegularMeromorphicSection (flatComponent pX η).X
      ((Modules.pullback ((flatComponent pX η).ι ≫ f)).obj L)
      (meromorphicSectionPullbackToFlatComponent pX f r L s η) :=
  sorry

/-- The cycle `n_i (X_i → X)_* div_{f^* L|_{X_i}}(s_i)` of the pulled-back
meromorphic section on an irreducible component of `X`. -/
noncomputable def flatComponentMeromorphicDivisor {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) [IsIntegral Y]
    (L : Y.Modules) [isInvertibleObject L]
    (s : meromorphicSections Y L) (hs : IsRegularMeromorphicSection Y L s)
    (η : genericPoints X) :
    Function.locallyFinsupp (Points X) ℤ :=
  (@ClosedSubspace.componentMultiplicity S X
      (LocallyOfFiniteType.isLocallyNoetherian pX) (ClosedSubspace.id X) η : ℤ) •
    closedImmersionPushforwardCycle (flatComponent pX η)
      (meromorphicSectionDivisorCycle ((flatComponent pX η).ι ≫ pX) δ
        (meromorphicSectionPullbackToFlatComponent pX f r L s η)
        (isRegularMeromorphicSection_flatComponent pX f r L s hs η))

/-- A component meromorphic divisor cycle is the multiplicity-weighted
closed-immersion pushforward of `div_{f^* L|_{X_i}}(s_i)`. -/
theorem flatComponentMeromorphicDivisor_eq {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) [IsIntegral Y]
    (L : Y.Modules) [isInvertibleObject L]
    (s : meromorphicSections Y L) (hs : IsRegularMeromorphicSection Y L s)
    (η : genericPoints X) :
    flatComponentMeromorphicDivisor pY pX δ f r hf L s hs η =
      (@ClosedSubspace.componentMultiplicity S X
          (LocallyOfFiniteType.isLocallyNoetherian pX)
          (ClosedSubspace.id X) η : ℤ) •
        closedImmersionPushforwardCycle (flatComponent pX η)
          (meromorphicSectionDivisorCycle ((flatComponent pX η).ι ≫ pX) δ
            (meromorphicSectionPullbackToFlatComponent pX f r L s η)
            (isRegularMeromorphicSection_flatComponent pX f r L s hs η)) :=
  sorry

/-- The family of multiplicity-weighted component meromorphic divisor cycles is
locally finite on `|X|`. -/
theorem locallyFinite_flatComponentMeromorphicDivisor {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) [IsIntegral Y]
    (L : Y.Modules) [isInvertibleObject L]
    (s : meromorphicSections Y L) (hs : IsRegularMeromorphicSection Y L s) :
    LocallyFinite fun η : genericPoints X ↦
      (flatComponentMeromorphicDivisor pY pX δ f r hf L s hs η).support :=
  sorry

/-- Lemma 82.19.1: In Situation 82.2.1 let `X, Y / B` be good. Let
`f : X ⟶ Y` be a flat morphism of relative dimension `r`. Let `L` be an
invertible sheaf on `Y`. Assume `Y` is integral and
`n = dim_δ(Y)`. Let `s` be a nonzero meromorphic section of `L`. Then
`f^* div_L(s) = ∑ n_i div_{f^* L|_{X_i}}(s_i)` in `Z_{n+r-1}(X)`. The sum
is over the irreducible components `X_i ⊂ X` of `δ`-dimension `n + r`, the
section `s_i = f|_{X_i}^*(s)` is the pullback of `s`, and `n_i = m_{X_i,X}`
is the multiplicity of `X_i` in `X`. -/
@[stacks 0EQQ]
theorem flatPullback_meromorphicSectionDivisor {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) [IsIntegral Y] (n : ℤ)
    (hY : deltaDimension pY δ (univIrreducibleClosed Y) = n)
    (L : Y.Modules) [isInvertibleObject L]
    (s : meromorphicSections Y L) (hs : IsRegularMeromorphicSection Y L s) :
    flatPullback pY pX δ f r hf (n - 1)
        (meromorphicSectionDivisorCycle pY δ s hs) =
      AlgebraicCycle.locallyFiniteSum
        (fun η : genericPoints X ↦
          flatComponentMeromorphicDivisor pY pX δ f r hf L s hs η)
        (locallyFinite_flatComponentMeromorphicDivisor pY pX δ f r hf L s hs) :=
  sorry

/-- The flat pullback of `div_L(s)` is an `(n + r - 1)`-cycle on `X`. -/
theorem flatPullback_meromorphicSectionDivisor_mem_cycleGroup {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) [IsIntegral Y] (n : ℤ)
    (hY : deltaDimension pY δ (univIrreducibleClosed Y) = n)
    (L : Y.Modules) [isInvertibleObject L]
    (s : meromorphicSections Y L) (hs : IsRegularMeromorphicSection Y L s) :
    flatPullback pY pX δ f r hf (n - 1)
        (meromorphicSectionDivisorCycle pY δ s hs) ∈
      (cycleGroup pX) δ (n + (r : ℤ) - 1) :=
  sorry

/-- The multiplicity-weighted sum of component meromorphic divisor cycles is an
`(n + r - 1)`-cycle on `X`. -/
theorem flatComponentMeromorphicDivisorSum_mem_cycleGroup {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) [IsIntegral Y] (n : ℤ)
    (hY : deltaDimension pY δ (univIrreducibleClosed Y) = n)
    (L : Y.Modules) [isInvertibleObject L]
    (s : meromorphicSections Y L) (hs : IsRegularMeromorphicSection Y L s) :
    AlgebraicCycle.locallyFiniteSum
        (fun η : genericPoints X ↦
          flatComponentMeromorphicDivisor pY pX δ f r hf L s hs η)
        (locallyFinite_flatComponentMeromorphicDivisor pY pX δ f r hf L s hs) ∈
      (cycleGroup pX) δ (n + (r : ℤ) - 1) :=
  sorry

/-- An irreducible component of `X` has `δ`-dimension `n + r` when `Y` is
integral of `δ`-dimension `n` and `f` is flat of relative dimension `r`. -/
theorem flatComponent_deltaDimension {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) [IsIntegral Y] (n : ℤ)
    (hY : deltaDimension pY δ (univIrreducibleClosed Y) = n)
    (η : genericPoints X) :
    deltaDimension ((flatComponent pX η).ι ≫ pX) δ
      (univIrreducibleClosed (flatComponent pX η).X) = n + (r : ℤ) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
