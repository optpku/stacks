module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.EulerComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections

/-!
# Euler characteristics over a field

This leaf owns the Euler characteristic of a coherent scheme module on a
scheme proper over a field.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k]
variable {X : Scheme.{u}}

/-- The Euler characteristic of a coherent module on a scheme proper over a field, defined as
the signed finite sum of the dimensions of its cohomology groups. -/
@[stacks 0BEJ]
noncomputable def eulerCharacteristic
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (F : X.Modules) [F.IsCoherent] : ℤ :=
  GradedObject.eulerChar (ComplexShape.up ℕ)
    (fun i : ℕ => cohomology f F i)

/-- Unfold the Euler characteristic into the signed finite sum of cohomology dimensions. -/
@[stacks 0BEJ]
theorem eulerCharacteristic_def
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (F : X.Modules) [F.IsCoherent] :
    eulerCharacteristic f F =
      ∑ᶠ i : ℕ,
        ((i : ℤ).negOnePow : ℤ) * (cohomologyFinrank f F i : ℤ) := by
  simp [eulerCharacteristic, GradedObject.eulerChar,
    cohomologyFinrank, ComplexShape.eulerCharSignsUpNat_χ,
    Units.val_pow_eq_pow_val, Int.coe_negOnePow_natCast]


/-- The Euler characteristic is additive along a short exact complex of coherent modules on a
scheme proper over a field. -/
@[stacks 08AA]
theorem eulerCharacteristic_eq_add_of_shortExact
    {S : ShortComplex X.Modules}
    [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (hS : S.ShortExact) :
    eulerCharacteristic f S.X₂ =
      eulerCharacteristic f S.X₁ + eulerCharacteristic f S.X₃ := sorry

/-- Euler characteristic depends only on the coefficient-sheaf isomorphism class. -/
theorem eulerCharacteristic_eq_of_iso
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    {F G : X.Modules} [F.IsCoherent] [G.IsCoherent] (e : F ≅ G) :
    eulerCharacteristic f F = eulerCharacteristic f G :=
  GradedObject.eulerChar_eq_of_iso (ComplexShape.up ℕ)
    (fun i => (cohomologyFunctor f i).mapIso e)

/-- Any cohomological bound, in any dimension, converts the full Euler characteristic
to a finite truncation. The vanishing is an explicit input; no curve vanishing is asserted. -/
theorem eulerCharacteristic_eq_sum_range
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (F : X.Modules) [F.IsCoherent] (n : ℕ)
    (h : ∀ i, n ≤ i → Limits.IsZero (cohomology f F i)) :
    eulerCharacteristic f F =
      ∑ i ∈ Finset.range n, (-1 : ℤ) ^ i * (cohomologyFinrank f F i : ℤ) :=
  GradedObject.eulerChar_eq_sum_range_of_isZero _ n h

/-- The two-term formula for any sheaf whose higher cohomology vanishes. -/
theorem eulerCharacteristic_eq_finrank_zero_sub_one
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (F : X.Modules) [F.IsCoherent]
    (h : ∀ i, 2 ≤ i → Limits.IsZero (cohomology f F i)) :
    eulerCharacteristic f F =
      (cohomologyFinrank f F 0 : ℤ) - (cohomologyFinrank f F 1 : ℤ) := by
  rw [eulerCharacteristic_eq_sum_range f F 2 h]
  simp [Finset.sum_range_succ, sub_eq_add_neg]

end AlgebraicGeometry.Scheme.Hom
