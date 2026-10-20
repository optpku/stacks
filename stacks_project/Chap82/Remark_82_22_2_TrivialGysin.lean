/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap82.Definition_82_22_1_Gysin

/-!
# Cycle-level Gysin maps for trivial restrictions on algebraic spaces

When an invertible module restricts to a unit on the zero scheme of a global
section, the refined Gysin homomorphism of Definition 82.22.1 lifts to a
canonical additive map on cycles, sending generators contained in the zero
scheme to zero.
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
  sorry

/-- A generator away from `Z(s)` contributes the associated cycle of
`Z(s) ∩ closure({x})`. -/
theorem trivialGysinGeneratorCycle_of_not_mem (x : Points X)
    (hx : (Hom.relativeDimensionFunction (f)) δ x = k + 1)
    (hmem : x ∉ (zeroScheme L s).pointsSet) :
    trivialGysinGeneratorCycle f δ k L s htriv x hx =
      gysinIntersectionCycle f δ k L s x :=
  sorry

/-- The coefficient-weighted trivial-restriction Gysin generator cycles form a
locally finite family on `Z(s)`. -/
theorem trivialGysinGeneratorTermsLocallyFinite
    (α : Function.locallyFinsupp (Points X) ℤ) :
    LocallyFinite fun x : Points X ↦
      (if hx : (Hom.relativeDimensionFunction (f)) δ x = k + 1 then
        α x • trivialGysinGeneratorCycle f δ k L s htriv x hx
      else 0).support :=
  sorry

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
  sorry

/-- The trivial-restriction Gysin cycle of a `(k + 1)`-cycle is a `k`-cycle on
`Z(s)`. -/
theorem trivialGysinCycle_mem (α : (Hom.cycleGroup (f)) δ (k + 1)) :
    trivialGysinCycle f δ k L s htriv (α : Function.locallyFinsupp (Points X) ℤ) ∈
      (Hom.cycleGroup (zeroSchemeι L s ≫ f)) δ k :=
  sorry

/-- The concrete trivial-restriction Gysin cycle sends zero to zero. -/
theorem trivialGysinCycle_zero :
    trivialGysinCycle f δ k L s htriv (0 : Function.locallyFinsupp (Points X) ℤ) =
      0 :=
  sorry

/-- The concrete trivial-restriction Gysin cycle preserves addition. -/
theorem trivialGysinCycle_add (α β : Function.locallyFinsupp (Points X) ℤ) :
    trivialGysinCycle f δ k L s htriv (α + β) =
      trivialGysinCycle f δ k L s htriv α +
        trivialGysinCycle f δ k L s htriv β :=
  sorry

/-- The canonical additive cycle map associated to a section whose invertible
module becomes a unit on its zero scheme. -/
noncomputable def trivialGysin :
    (Hom.cycleGroup (f)) δ (k + 1) →+ (Hom.cycleGroup (zeroSchemeι L s ≫ f)) δ k where
  toFun := fun α ↦
    ⟨trivialGysinCycle f δ k L s htriv (α : Function.locallyFinsupp (Points X) ℤ),
      trivialGysinCycle_mem f δ k L s htriv α⟩
  map_zero' := sorry
  map_add' := sorry

/-- On a point generator contained in `Z(s)`, the trivial-restriction Gysin map
is zero. -/
theorem trivialGysin_point_of_mem (x : Points X)
    (hx : (Hom.relativeDimensionFunction (f)) δ x = k + 1)
    (hmem : x ∈ (zeroScheme L s).pointsSet) :
    trivialGysin f δ k L s htriv ⟨pointCycle x, pointCycle_mem f δ k x hx⟩ = 0 :=
  sorry

/-- On a point generator away from `Z(s)`, the trivial-restriction Gysin map is
the associated cycle of `Z(s) ∩ closure({x})`. -/
theorem trivialGysin_point_of_not_mem (x : Points X)
    (hx : (Hom.relativeDimensionFunction (f)) δ x = k + 1)
    (hmem : x ∉ (zeroScheme L s).pointsSet) :
    trivialGysin f δ k L s htriv ⟨pointCycle x, pointCycle_mem f δ k x hx⟩ =
      ⟨gysinIntersectionCycle f δ k L s x,
        gysinIntersectionCycle_mem f δ k L s x⟩ :=
  sorry

/-- Passage to Chow classes identifies the trivial-restriction cycle map with
the refined Gysin homomorphism. -/
theorem trivialGysin_chowClass (α : (Hom.cycleGroup (f)) δ (k + 1)) :
    (Hom.chowMk (zeroSchemeι L s ≫ f)) δ k (trivialGysin f δ k L s htriv α) =
      gysin f δ k L s α :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
