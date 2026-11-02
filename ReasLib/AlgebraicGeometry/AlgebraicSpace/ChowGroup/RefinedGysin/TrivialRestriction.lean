/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin

/-!
# Cycle-level Gysin maps for trivial restrictions on algebraic spaces

When an invertible module restricts to a unit on the zero scheme of a global
section, the refined Gysin homomorphism lifts to a canonical additive map on
cycles, sending generators contained in the zero scheme to zero.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open Function Set Topology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (k : ℤ)
variable (L : X.Modules) [isInvertibleObject L] (s : L.sections)
variable (htriv : isUnitObject ((Modules.pullback (zeroSchemeι L s)).obj L))

/-- The cycle contributed by a degree-`k + 1` point when the restriction of `L`
to `Z(s)` is a unit: it is zero on `Z(s)` and the scheme-theoretic intersection
cycle away from `Z(s)`. -/
noncomputable def trivialGysinGeneratorCycle (x : Points X)
    (hx : (Hom.relativeDimensionFunction (f)) δ x = k + 1) :
    Function.locallyFinsupp (Points (zeroScheme L s).X) ℤ :=
  let _ := htriv
  let _ := hx
  @dite (Function.locallyFinsupp (Points (zeroScheme L s).X) ℤ)
    (x ∈ (zeroScheme L s).pointsSet) (Classical.propDecidable _)
    (fun _ ↦ 0)
    (fun _ ↦ gysinIntersectionCycle f δ k L s x)

/-- A generator supported on `Z(s)` contributes zero to the trivial-restriction
Gysin cycle. -/
theorem trivialGysinGeneratorCycle_of_mem (x : Points X)
    (hx : (Hom.relativeDimensionFunction (f)) δ x = k + 1)
    (hmem : x ∈ (zeroScheme L s).pointsSet) :
    trivialGysinGeneratorCycle f δ k L s htriv x hx = 0 :=
  by simp [trivialGysinGeneratorCycle, hmem]

/-- A generator away from `Z(s)` contributes the associated cycle of
`Z(s) ∩ closure({x})`. -/
theorem trivialGysinGeneratorCycle_of_not_mem (x : Points X)
    (hx : (Hom.relativeDimensionFunction (f)) δ x = k + 1)
    (hmem : x ∉ (zeroScheme L s).pointsSet) :
    trivialGysinGeneratorCycle f δ k L s htriv x hx =
      gysinIntersectionCycle f δ k L s x :=
  by simp [trivialGysinGeneratorCycle, hmem]

/-- The coefficient-weighted trivial-restriction Gysin generator cycles form a
locally finite family on `Z(s)`. -/
theorem trivialGysinGeneratorTermsLocallyFinite
    (α : Function.locallyFinsupp (Points X) ℤ) :
    LocallyFinite fun x : Points X ↦
      (if hx : (Hom.relativeDimensionFunction (f)) δ x = k + 1 then
        α x • trivialGysinGeneratorCycle f δ k L s htriv x hx
      else 0).support :=
  by
    classical
    apply (ChowGroup.RefinedGysin.generatorTermsLocallyFinite f δ L s k α).subset
    intro x z hz
    by_cases hx : Hom.relativeDimensionFunction f δ x = k + 1
    · by_cases hmem : x ∈ (zeroScheme L s).pointsSet
      · simp [hx, trivialGysinGeneratorCycle, hmem] at hz
      · simpa [hx, trivialGysinGeneratorCycle, hmem,
          ChowGroup.RefinedGysin.generator_of_not_mem f δ L s k x hmem] using hz
    · simp [hx] at hz

/-- The explicit locally finite cycle on `Z(s)` obtained by extending the
trivial-restriction generator rule linearly. -/
noncomputable def trivialGysinCycle (α : Function.locallyFinsupp (Points X) ℤ) :
    Function.locallyFinsupp (Points (zeroScheme L s).X) ℤ :=
  AlgebraicCycle.locallyFiniteSum
    (fun x : Points X ↦
      if hx : (Hom.relativeDimensionFunction (f)) δ x = k + 1 then
        α x • trivialGysinGeneratorCycle f δ k L s htriv x hx
      else 0)
    (trivialGysinGeneratorTermsLocallyFinite f δ k L s htriv α)

/-- Coefficients of the trivial-restriction Gysin cycle are the pointwise finite
sums of the weighted generator cycles. -/
theorem trivialGysinCycle_apply (α : Function.locallyFinsupp (Points X) ℤ)
    (z : Points (zeroScheme L s).X) :
    trivialGysinCycle f δ k L s htriv α z =
      ∑ᶠ x : Points X,
        (if hx : (Hom.relativeDimensionFunction (f)) δ x = k + 1 then
          α x • trivialGysinGeneratorCycle f δ k L s htriv x hx
        else 0) z :=
  rfl

/-- The trivial-restriction Gysin cycle of a `(k + 1)`-cycle is a `k`-cycle on
`Z(s)`. -/
theorem trivialGysinCycle_mem (α : (Hom.cycleGroup (f)) δ (k + 1)) :
    trivialGysinCycle f δ k L s htriv (α : Function.locallyFinsupp (Points X) ℤ) ∈
      (Hom.cycleGroup (zeroSchemeι L s ≫ f)) δ k :=
  by
    classical
    letI : IsLocallyNoetherian (zeroScheme L s).X :=
      LocallyOfFiniteType.isLocallyNoetherian (zeroSchemeι L s ≫ f)
    intro z hz
    by_contra hdegree
    apply hz
    rw [trivialGysinCycle_apply]
    apply finsum_eq_zero_of_forall_eq_zero
    intro x
    by_cases hx : Hom.relativeDimensionFunction f δ x = k + 1
    · by_cases hmem : x ∈ (zeroScheme L s).pointsSet
      · simp [hx, trivialGysinGeneratorCycle, hmem]
      · have hi : gysinIntersectionCycle f δ k L s x z = 0 :=
          ClosedSubspace.associatedCycle_eq_zero_of_dimension_ne _ _ _ hdegree
        simp [hx, trivialGysinGeneratorCycle, hmem,
          Function.locallyFinsuppWithin.coe_zsmul, hi]
    · simp [hx]

/-- The concrete trivial-restriction Gysin cycle sends zero to zero. -/
theorem trivialGysinCycle_zero :
    trivialGysinCycle f δ k L s htriv (0 : Function.locallyFinsupp (Points X) ℤ) =
      0 :=
  by
    ext z
    rw [trivialGysinCycle_apply]
    simp

/-- The concrete trivial-restriction Gysin cycle preserves addition. -/
theorem trivialGysinCycle_add (α β : Function.locallyFinsupp (Points X) ℤ) :
    trivialGysinCycle f δ k L s htriv (α + β) =
      trivialGysinCycle f δ k L s htriv α +
        trivialGysinCycle f δ k L s htriv β :=
  by
    classical
    ext z
    change trivialGysinCycle f δ k L s htriv (α + β) z =
      trivialGysinCycle f δ k L s htriv α z + trivialGysinCycle f δ k L s htriv β z
    rw [trivialGysinCycle_apply, trivialGysinCycle_apply, trivialGysinCycle_apply]
    have hterm : ∀ x : Points X,
        (if hx : Hom.relativeDimensionFunction f δ x = k + 1 then
          (α + β) x • trivialGysinGeneratorCycle f δ k L s htriv x hx else 0) z =
        (if hx : Hom.relativeDimensionFunction f δ x = k + 1 then
          α x • trivialGysinGeneratorCycle f δ k L s htriv x hx else 0) z +
        (if hx : Hom.relativeDimensionFunction f δ x = k + 1 then
          β x • trivialGysinGeneratorCycle f δ k L s htriv x hx else 0) z := by
      intro x
      by_cases hx : Hom.relativeDimensionFunction f δ x = k + 1
      · simp [hx, add_smul, Function.locallyFinsuppWithin.coe_zsmul]
      · simp [hx]
    simp_rw [hterm]
    exact finsum_add_distrib
      ((trivialGysinGeneratorTermsLocallyFinite f δ k L s htriv α).point_finite z)
      ((trivialGysinGeneratorTermsLocallyFinite f δ k L s htriv β).point_finite z)

/-- The canonical additive cycle map associated to a section whose invertible
module becomes a unit on its zero scheme. -/
noncomputable def trivialGysin :
    (Hom.cycleGroup (f)) δ (k + 1) →+ (Hom.cycleGroup (zeroSchemeι L s ≫ f)) δ k where
  toFun := fun α ↦
    ⟨trivialGysinCycle f δ k L s htriv (α : Function.locallyFinsupp (Points X) ℤ),
      trivialGysinCycle_mem f δ k L s htriv α⟩
  map_zero' := Subtype.ext (trivialGysinCycle_zero f δ k L s htriv)
  map_add' α β := Subtype.ext (trivialGysinCycle_add f δ k L s htriv α β)

private theorem trivialGysinCycle_pointCycle (x : Points X)
    (hx : Hom.relativeDimensionFunction f δ x = k + 1) :
    trivialGysinCycle f δ k L s htriv (pointCycle x) =
      trivialGysinGeneratorCycle f δ k L s htriv x hx := by
  classical
  ext z
  rw [trivialGysinCycle_apply, finsum_eq_single _ x]
  · simp [pointCycle, hx, Function.locallyFinsuppWithin.single_apply]
  · intro y hy
    by_cases hdegree : Hom.relativeDimensionFunction f δ y = k + 1
    · simp [hdegree, pointCycle, Function.locallyFinsuppWithin.single_apply, hy]
    · simp [hdegree]

/-- On a point generator contained in `Z(s)`, the trivial-restriction Gysin map
is zero. -/
theorem trivialGysin_point_of_mem (x : Points X)
    (hx : (Hom.relativeDimensionFunction (f)) δ x = k + 1)
    (hmem : x ∈ (zeroScheme L s).pointsSet) :
    trivialGysin f δ k L s htriv ⟨pointCycle x, pointCycle_mem f δ k x hx⟩ = 0 :=
  by
    apply Subtype.ext
    change trivialGysinCycle f δ k L s htriv (pointCycle x) = 0
    rw [trivialGysinCycle_pointCycle f δ k L s htriv x hx,
      trivialGysinGeneratorCycle_of_mem f δ k L s htriv x hx hmem]

/-- On a point generator away from `Z(s)`, the trivial-restriction Gysin map is
the associated cycle of `Z(s) ∩ closure({x})`. -/
theorem trivialGysin_point_of_not_mem (x : Points X)
    (hx : (Hom.relativeDimensionFunction (f)) δ x = k + 1)
    (hmem : x ∉ (zeroScheme L s).pointsSet) :
    trivialGysin f δ k L s htriv ⟨pointCycle x, pointCycle_mem f δ k x hx⟩ =
      ⟨gysinIntersectionCycle f δ k L s x,
        gysinIntersectionCycle_mem f δ k L s x⟩ :=
  by
    apply Subtype.ext
    change trivialGysinCycle f δ k L s htriv (pointCycle x) = _
    rw [trivialGysinCycle_pointCycle f δ k L s htriv x hx]
    exact trivialGysinGeneratorCycle_of_not_mem f δ k L s htriv x hx hmem

/-- Passage to Chow classes identifies the trivial-restriction cycle map with
the refined Gysin homomorphism. -/
theorem trivialGysin_chowClass (α : (Hom.cycleGroup (f)) δ (k + 1)) :
    (Hom.chowMk (zeroSchemeι L s ≫ f)) δ k (trivialGysin f δ k L s htriv α) =
      gysin f δ k L s α :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
