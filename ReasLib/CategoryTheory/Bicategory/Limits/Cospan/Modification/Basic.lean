module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Basic cospan modification operations

`Cospan.Basic` owns the walking-cospan transformation and its vertex projections. This leaf
adds the corresponding vertex projections and generator naturality API for modifications,
together with the canonical identity and vertical-composition operations. The finite
walking-cospan assembly of a modification is layered in `Modification.Construction`, and its
readout equations are in `Modification.Computations`.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe w v u

namespace CategoryTheory.Bicategory.CospanTransform.Hom

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z x' y' z' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}
variable {ψ φ : CospanTransform f g f' g'}

/-- The component of a cospan modification at the left endpoint. -/
abbrev left (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) : ψ.left ⟶ φ.left :=
  Γ.as.app (LocallyDiscrete.mk Limits.WalkingCospan.left)

/-- The component of a cospan modification at the right endpoint. -/
abbrev right (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) : ψ.right ⟶ φ.right :=
  Γ.as.app (LocallyDiscrete.mk Limits.WalkingCospan.right)

/-- The component of a cospan modification at the common target. -/
abbrev base (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) : ψ.base ⟶ φ.base :=
  Γ.as.app (LocallyDiscrete.mk Limits.WalkingCospan.one)

/-- Naturality of a cospan modification on the left generating arrow. -/
@[reassoc]
theorem left_naturality (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    left Γ ▷ f' ≫ φ.leftIso.hom =
      ψ.leftIso.hom ≫ f ◁ base Γ := sorry

/-- Naturality on the left generator, solved in the inverse orientation. -/
@[reassoc]
theorem left_naturality_inv (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    ψ.leftIso.inv ≫ left Γ ▷ f' =
      f ◁ base Γ ≫ φ.leftIso.inv := sorry

/-- Naturality of a cospan modification on the right generating arrow. -/
@[reassoc]
theorem right_naturality (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    right Γ ▷ g' ≫ φ.rightIso.hom =
      ψ.rightIso.hom ≫ g ◁ base Γ := sorry

/-- Naturality on the right generator, solved in the inverse orientation. -/
@[reassoc]
theorem right_naturality_inv (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    ψ.rightIso.inv ≫ right Γ ▷ g' =
      g ◁ base Γ ≫ φ.rightIso.inv := sorry

/-- Modifications between cospan transformations are determined by their three vertex
components. -/
@[ext]
theorem ext
    (Γ Δ : Pseudofunctor.StrongTrans.Hom ψ φ)
    (leftEq : left Γ = left Δ) (rightEq : right Γ = right Δ)
    (baseEq : base Γ = base Δ) :
    Γ = Δ := sorry

/-- The identity modification of a cospan transformation. -/
def id (ψ : CospanTransform f g f' g') :
    Pseudofunctor.StrongTrans.Hom ψ ψ :=
  ⟨Pseudofunctor.StrongTrans.Modification.id ψ⟩

/-- Vertical composition of cospan modifications. -/
def comp
    {χ : CospanTransform f g f' g'}
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ)
    (Δ : Pseudofunctor.StrongTrans.Hom φ χ) :
    Pseudofunctor.StrongTrans.Hom ψ χ :=
  ⟨Pseudofunctor.StrongTrans.Modification.vcomp Γ.as Δ.as⟩

/- Data audit (mathlib 4.32): `left`, `right`, and `base` are direct evaluations of a
modification. `id` and `comp` delegate to the canonical strong-transformation modification
operations, so this leaf introduces no non-`Prop` choices. -/

end CategoryTheory.Bicategory.CospanTransform.Hom
