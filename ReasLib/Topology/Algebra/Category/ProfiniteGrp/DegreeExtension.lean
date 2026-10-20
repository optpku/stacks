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

/-- The inclusion homomorphism `G →* Γ`. -/
noncomputable def inlHom : S.G →* S.middle :=
  S.kerClosed.subtype

/-- The inclusion `G →ₜ* Γ` of the kernel of `deg`. -/
noncomputable def inl : S.G →ₜ* S.middle :=
  ⟨S.kerClosed.subtype, continuous_subtype_val⟩

/-- The degree map is constant on conjugacy classes, since the profinite integers
are abelian. -/
theorem deg_eq_of_isConj {a b : S.middle} (h : IsConj a b) :
    S.deg a = S.deg b := sorry

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
  sorry

/-- Any two degree-one lifts differ by an element of `G = ker(deg)`. -/
theorem degreeOneLift_spec (γ : S.middle) :
    S.deg γ = hatZOne.{u} ↔ ∃ g : S.G, γ = S.inl g * S.degreeOneLift :=
  sorry

/-- The conjugacy class of a chosen degree-one lift, recording `F = 1` in `Γ/G = hatZ`. -/
noncomputable def frobenius : ConjClasses S.middle :=
  ConjClasses.mk S.degreeOneLift

/-- Conjugation by `γ` on the kernel of `deg`. -/
noncomputable def conjHom (γ : S.middle) : S.G →ₜ* S.G :=
  ⟨{ toFun := fun g => ⟨γ * g.val * γ⁻¹, sorry⟩
     map_one' := sorry
     map_mul' := sorry },
    sorry⟩

/-- Conjugation has the specified ambient group operation as its actual value. -/
@[simp]
theorem conjHom_val (γ : S.middle) (g : S.G) :
    (S.conjHom γ g).val = γ * g.val * γ⁻¹ := rfl

/-- Package a surjective degree map as a degree extension. -/
noncomputable def ofSurjectiveDeg (middle : ProfiniteGrp.{u}) (deg : middle ⟶ hatZ.{u})
    (h : Function.Surjective deg) : DegreeExtension.{u} where
  middle := middle
  deg := deg
  deg_surjective := h

end DegreeExtension

end ProfiniteGrp
