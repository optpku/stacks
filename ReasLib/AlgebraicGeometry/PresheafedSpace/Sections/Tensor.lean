/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Tensor and pushout comparison maps for sections

The constructions in this file only require a commutative-ring-valued
presheafed space.  Scheme-level names at the end are thin specializations.
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.PresheafedSpace

/-- The canonical map from the tensor product of sections on two opens to sections on their
intersection, obtained by restricting both factors and multiplying. -/
@[stacks 01KP "tensor-product map to sections on an intersection"]
def sectionTensorToIntersection
    {X : PresheafedSpace.{u} CommRingCat.{u}} (U V : Opens X) :
    CommRingCat.of
        (TensorProduct ℤ (X.presheaf.obj (op U) : Type u)
          (X.presheaf.obj (op V) : Type u)) ⟶
      X.presheaf.obj (op (U ⊓ V)) :=
  CommRingCat.ofHom <|
    (Algebra.TensorProduct.productMap
      (CommRingCat.Hom.hom
        (X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op)).toIntAlgHom
      (CommRingCat.Hom.hom
        (X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op)).toIntAlgHom).toRingHom

/-- On a pure tensor, the comparison map is the product of the two restricted sections. -/
@[simp]
theorem sectionTensorToIntersection_tmul
    {X : PresheafedSpace.{u} CommRingCat.{u}} (U V : Opens X)
    (s : X.presheaf.obj (op U)) (t : X.presheaf.obj (op V)) :
    (sectionTensorToIntersection U V).hom (s ⊗ₜ[ℤ] t) =
      (X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom s *
        (X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom t := sorry

end AlgebraicGeometry.PresheafedSpace

namespace AlgebraicGeometry.PresheafedSpace.Hom

variable {X S : PresheafedSpace.{u} CommRingCat.{u}}

/-- The map on sections from a target open `W` to a source open `U` contained in its preimage. -/
def appLE (f : X ⟶ S) (W : Opens S) (U : Opens X)
    (hU : U ≤ (Opens.map f.base).obj W) :
    S.presheaf.obj (op W) ⟶ X.presheaf.obj (op U) :=
  f.c.app (op W) ≫ X.presheaf.map (homOfLE hU).op

/-- Restricting the target of an `appLE` map composes with the corresponding presheaf
restriction. -/
@[reassoc (attr := simp)]
theorem appLE_map (f : X ⟶ S) (W : Opens S) (U U' : Opens X)
    (hU : U ≤ (Opens.map f.base).obj W) (hU' : U' ≤ U) :
    f.appLE W U hU ≫ X.presheaf.map (homOfLE hU').op =
      f.appLE W U' (hU'.trans hU) := sorry

/-- Pulling sections from `W` through `U` or `V` gives the same map after restriction to
`U ⊓ V`. -/
theorem appLE_restrict_inter_comm
    (f : X ⟶ S) (U V : Opens X) (W : Opens S)
    (hU : U ≤ (Opens.map f.base).obj W)
    (hV : V ≤ (Opens.map f.base).obj W) :
    f.appLE W U hU ≫ X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op =
      f.appLE W V hV ≫
        X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op := sorry

/-- The canonical map from the pushout of section rings over `Γ(S, W)` to sections on `U ⊓ V`;
this is the relative algebraic owner used in Lemma 26.21.7. -/
@[stacks 01KP]
noncomputable def sectionPushoutToIntersection
    (f : X ⟶ S) (U V : Opens X) (W : Opens S)
    (hU : U ≤ (Opens.map f.base).obj W)
    (hV : V ≤ (Opens.map f.base).obj W) :
    pushout (f.appLE W U hU) (f.appLE W V hV) ⟶
      X.presheaf.obj (op (U ⊓ V)) :=
  pushout.desc
    (X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op)
    (X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op)
    (f.appLE_restrict_inter_comm U V W hU hV)

/-- The left pushout factor of `sectionPushoutToIntersection` is restriction from `U`. -/
@[reassoc (attr := simp)]
theorem sectionPushoutToIntersection_inl
    (f : X ⟶ S) (U V : Opens X) (W : Opens S)
    (hU : U ≤ (Opens.map f.base).obj W)
    (hV : V ≤ (Opens.map f.base).obj W) :
    pushout.inl (f.appLE W U hU) (f.appLE W V hV) ≫
        f.sectionPushoutToIntersection U V W hU hV =
      X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op := sorry

/-- The right pushout factor of `sectionPushoutToIntersection` is restriction from `V`. -/
@[reassoc (attr := simp)]
theorem sectionPushoutToIntersection_inr
    (f : X ⟶ S) (U V : Opens X) (W : Opens S)
    (hU : U ≤ (Opens.map f.base).obj W)
    (hV : V ≤ (Opens.map f.base).obj W) :
    pushout.inr (f.appLE W U hU) (f.appLE W V hV) ≫
        f.sectionPushoutToIntersection U V W hU hV =
      X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op := sorry

/-- The canonical quotient from the absolute tensor product over `ℤ` to the relative section
ring pushout over `Γ(S, W)`. -/
noncomputable def sectionTensorToPushout
    (f : X ⟶ S) (U V : Opens X) (W : Opens S)
    (hU : U ≤ (Opens.map f.base).obj W)
    (hV : V ≤ (Opens.map f.base).obj W) :
    CommRingCat.of
        (TensorProduct ℤ (X.presheaf.obj (op U) : Type u)
          (X.presheaf.obj (op V) : Type u)) ⟶
      pushout (f.appLE W U hU) (f.appLE W V hV) :=
  CommRingCat.ofHom <|
    (Algebra.TensorProduct.productMap
      (pushout.inl (f.appLE W U hU) (f.appLE W V hV)).hom.toIntAlgHom
      (pushout.inr (f.appLE W U hU) (f.appLE W V hV)).hom.toIntAlgHom).toRingHom

/-- The canonical map from the absolute tensor product to the relative pushout is surjective. -/
theorem sectionTensorToPushout_surjective
    (f : X ⟶ S) (U V : Opens X) (W : Opens S)
    (hU : U ≤ (Opens.map f.base).obj W)
    (hV : V ≤ (Opens.map f.base).obj W) :
    Function.Surjective (f.sectionTensorToPushout U V W hU hV).hom := sorry

/-- The absolute tensor comparison factors through the relative pushout comparison. -/
theorem sectionTensorToPushout_comp_sectionPushoutToIntersection
    (f : X ⟶ S) (U V : Opens X) (W : Opens S)
    (hU : U ≤ (Opens.map f.base).obj W)
    (hV : V ≤ (Opens.map f.base).obj W) :
    f.sectionTensorToPushout U V W hU hV ≫
        f.sectionPushoutToIntersection U V W hU hV =
      PresheafedSpace.sectionTensorToIntersection U V := sorry

/-- Surjectivity of the relative section-ring comparison is equivalent to surjectivity of the
absolute tensor comparison. -/
theorem sectionPushoutToIntersection_surjective_iff
    (f : X ⟶ S) (U V : Opens X) (W : Opens S)
    (hU : U ≤ (Opens.map f.base).obj W)
    (hV : V ≤ (Opens.map f.base).obj W) :
    Function.Surjective (f.sectionPushoutToIntersection U V W hU hV).hom ↔
      Function.Surjective
        (PresheafedSpace.sectionTensorToIntersection U V).hom := sorry

end AlgebraicGeometry.PresheafedSpace.Hom

namespace AlgebraicGeometry.Scheme

variable {X S : Scheme.{u}}

/-- The section tensor-product comparison specialized to a scheme. -/
noncomputable abbrev sectionTensorToIntersection
    (X : Scheme.{u}) (U V : X.Opens) :=
  PresheafedSpace.sectionTensorToIntersection U V

namespace Hom

/-- The section-pushout comparison specialized to schemes. -/
noncomputable abbrev sectionPushoutToIntersection
    (f : X ⟶ S) (U V : X.Opens) (W : S.Opens)
    (hU : U ≤ f ⁻¹ᵁ W) (hV : V ≤ f ⁻¹ᵁ W) :=
  f.toPshHom.sectionPushoutToIntersection U V W hU hV

/-- The scheme-level relative pushout comparison is surjective exactly when the absolute tensor
comparison is surjective. -/
theorem sectionPushoutToIntersection_surjective_iff
    (f : X ⟶ S) (U V : X.Opens) (W : S.Opens)
    (hU : U ≤ f ⁻¹ᵁ W) (hV : V ≤ f ⁻¹ᵁ W) :
    Function.Surjective (f.sectionPushoutToIntersection U V W hU hV).hom ↔
      Function.Surjective (X.sectionTensorToIntersection U V).hom := sorry

end Hom
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/-- The presheafed-space section map specializes to the canonical scheme-level `appLE`. -/
@[simp]
theorem toPshHom_appLE (f : X ⟶ S) (W : S.Opens) (U : X.Opens)
    (hU : U ≤ (Opens.map f.base).obj W) :
    f.toPshHom.appLE W U hU = f.appLE W U hU := sorry

end AlgebraicGeometry.Scheme.Hom
