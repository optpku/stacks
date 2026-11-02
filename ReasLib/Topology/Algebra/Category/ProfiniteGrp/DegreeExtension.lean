/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.Conj
public import ReasLib.Topology.Algebra.Category.ProfiniteGrp.HatZ
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-!
# Degree extensions of the profinite integers

A continuous surjective degree map specifies its actual profinite middle group and closed kernel.
The field-specific Frobenius normalization and arithmetic geometric examples are separate inputs.
-/

@[expose] public section

open CategoryTheory
open scoped Topology

noncomputable section

universe u

namespace ProfiniteGrp

/-- A profinite extension `1 → G → Γ →deg hatZ → 1`, with `G` recovered as `ker(deg)`. -/
structure DegreeExtension where
  /-- The middle profinite group of the extension. -/
  middle : ProfiniteGrp.{u}
  /-- The degree homomorphism `Γ ⟶ hatZ`. -/
  deg : middle ⟶ hatZ.{u}
  /-- The degree homomorphism is surjective. -/
  deg_surjective : Function.Surjective deg

namespace DegreeExtension

variable (S : DegreeExtension.{u})

/-- The kernel of `deg` as a closed subgroup of `Γ`. -/
noncomputable def kerClosed : ClosedSubgroup S.middle where
  toSubgroup := MonoidHom.ker S.deg.hom.toMonoidHom
  isClosed' := IsClosed.preimage S.deg.hom.continuous
      (isClosed_singleton : IsClosed ({1} : Set hatZ.{u}))

/-- The kernel `G = ker(deg)`, as a topological group. -/
abbrev G : Type u := S.kerClosed.toSubgroup

/-- The inclusion `G →ₜ* Γ` of the kernel of `deg`. -/
noncomputable def inl : S.G →ₜ* S.middle :=
  ⟨S.kerClosed.subtype, continuous_subtype_val⟩

/-- The degree map is constant on conjugacy classes, since the profinite integers
are abelian. -/
theorem deg_eq_of_isConj {a b : S.middle} (h : IsConj a b) :
    S.deg a = S.deg b := by
  apply Subtype.ext
  funext H
  let π : hatZ.{u} →* (integerGroup.{u} ⧸ H.toSubgroup) :=
    { toFun := fun z ↦ z.val H
      map_one' := rfl
      map_mul' _ _ := rfl }
  exact (isConj_iff_eq (α := integerGroup.{u} ⧸ H.toSubgroup)).mp
    ((π.comp S.deg.hom.toMonoidHom).map_isConj h)

/-- The degree of a conjugacy class, well-defined because `hatZ` is abelian. -/
noncomputable def degClass (c : ConjClasses S.middle) : hatZ.{u} :=
  Quotient.lift S.deg (fun _ _ h ↦ deg_eq_of_isConj S h) c

/-- The degree of the canonical conjugacy class is its representative's degree. -/
@[simp]
theorem degClass_mk (g : S.middle) : S.degClass (ConjClasses.mk g) = S.deg g := rfl

/-- A chosen degree-one lift of `1` in `hatZ`. -/
noncomputable def degreeOneLift : S.middle :=
  Classical.choose (S.deg_surjective hatZOne)

/-- The chosen degree-one lift maps to `1` in `hatZ`. -/
theorem deg_degreeOneLift : S.deg S.degreeOneLift = hatZOne.{u} :=
  Classical.choose_spec (S.deg_surjective hatZOne)

/-- Any two degree-one lifts differ by an element of `G = ker(deg)`. -/
theorem degreeOneLift_spec (γ : S.middle) :
    S.deg γ = hatZOne.{u} ↔ ∃ g : S.G, γ = S.inl g * S.degreeOneLift := by
  constructor
  · intro hγ
    refine ⟨⟨γ * S.degreeOneLift⁻¹, ?_⟩, ?_⟩
    · change S.deg.hom (γ * S.degreeOneLift⁻¹) = 1
      rw [map_mul, map_inv, hγ, S.deg_degreeOneLift, mul_inv_cancel]
    · change γ = γ * S.degreeOneLift⁻¹ * S.degreeOneLift
      simp [mul_assoc]
  · rintro ⟨g, rfl⟩
    change S.deg.hom (g.val * S.degreeOneLift) = _
    rw [map_mul, show S.deg.hom g.val = 1 from g.property,
      one_mul, S.deg_degreeOneLift]

/-- Conjugation by `γ` on the kernel of `deg`. -/
noncomputable def conjHom (γ : S.middle) : S.G →ₜ* S.G :=
  ⟨{ toFun := fun g => ⟨γ * g.val * γ⁻¹, by
       change S.deg.hom (γ * g.val * γ⁻¹) = 1
       rw [map_mul, map_mul, map_inv, show S.deg.hom g.val = 1 from g.property]
       simp⟩
     map_one' := by
       apply Subtype.ext
       simp
     map_mul' := by
       intro a b
       apply Subtype.ext
       simp [mul_assoc] },
    by
      exact ((IsTopologicalGroup.continuous_conj γ).comp
        continuous_subtype_val).subtype_mk _⟩

/-- Conjugation has the specified ambient group operation as its actual value. -/
@[simp]
theorem conjHom_val (γ : S.middle) (g : S.G) :
    (S.conjHom γ g).val = γ * g.val * γ⁻¹ := rfl

end DegreeExtension

end ProfiniteGrp
