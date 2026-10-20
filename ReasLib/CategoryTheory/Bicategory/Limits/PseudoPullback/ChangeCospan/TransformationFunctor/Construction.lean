module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.Modification.Functoriality

/-!
# Constructing the changed-cospan transformation functor

For a fixed readable pseudopullback cone, this leaf packages change of cospan as an ordinary
functor in parallel cospan transformations and constructs its natural isomorphism with neutral
pseudocone postcomposition. Projection formulas are kept in `TransformationFunctor.Computations`.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory.CospanTransform

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z x' y' z' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}

/-- For a fixed readable pseudopullback cone, change of cospan is functorial in
parallel cospan transformations and their modifications.

The codomain is the hom-category of cone transformations with the original apex. The target
cospan legs are explicit because the fixed source cone does not determine them. -/
def changeCospan.transformation.functor
    (S : PseudoPullbackCone f g) (f' : x' ⟶ z') (g' : y' ⟶ z') :
    CospanTransform f g f' g' ⥤
      (Pseudofunctor.const
          (LocallyDiscrete Limits.WalkingCospan) S.pt ⟶
        cospan f' g') where
  obj ψ := (S.changeCospan ψ).toPseudoCone.π
  map Γ := changeCospan.modification Γ S
  map_id ψ := changeCospan.modification.id ψ S
  map_comp Γ Δ := changeCospan.modification.comp Γ Δ S

/-- The presentation comparisons intertwine the readable modification action with
neutral pseudocone postcomposition.

This formulation is independent of the functor packaging and can therefore be used by
downstream arguments that only manipulate individual modifications. -/
theorem changeCospan.presentation.modification.iso.hom_naturality
    (S : PseudoPullbackCone f g)
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ) :
    changeCospan.modification Γ S ≫
        (changeCospan.presentation.modification.iso S φ).hom =
      (changeCospan.presentation.modification.iso S ψ).hom ≫
        PseudoCone.postcomposeModification Γ S.toPseudoCone := sorry

/-- The presentation comparisons form a natural family between the readable and
neutral transformation functors. -/
theorem changeCospan.transformation.functor.iso.naturality
    (S : PseudoPullbackCone f g)
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ) :
    (changeCospan.transformation.functor S f' g').map Γ ≫
        (changeCospan.presentation.modification.iso S φ).hom =
      (changeCospan.presentation.modification.iso S ψ).hom ≫
        (PseudoCone.postcomposeTransformationFunctor
          (cospan f' g') S.toPseudoCone).map Γ := sorry

/-- The readable change-of-cospan functor is naturally isomorphic to neutral
pseudocone postcomposition in the diagram-transformation variable. -/
def changeCospan.transformation.functor.iso
    (S : PseudoPullbackCone f g) (f' : x' ⟶ z') (g' : y' ⟶ z') :
    changeCospan.transformation.functor S f' g' ≅
      PseudoCone.postcomposeTransformationFunctor
        (cospan f' g') S.toPseudoCone :=
  NatIso.ofComponents
    (fun ψ ↦ changeCospan.presentation.modification.iso S ψ)
    (fun Γ ↦
      changeCospan.transformation.functor.iso.naturality (f' := f') (g' := g') S Γ)

/- Data and axiom audit (mathlib 4.32):

`changeCospan.transformation.functor` uses the explicit readable object and modification actions.
`changeCospan.transformation.functor.iso` reuses the unique bundled presentation comparison at
every object. Deferred fields are functor laws and naturality equalities; no object,
transformation, modification, or isomorphism component is selected by a proof placeholder. -/

end Bicategory.PseudoPullbackCone

end CategoryTheory
