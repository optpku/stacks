module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Stage.Hom

/-!
# The category of scheduled separating refinement stages

This leaf supplies identity and composition for scheduled-stage morphisms and
packages them as the canonical category structure.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v q r r'

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation

variable {C : Type u} [Category.{v} C]

section Stage

variable {ι : Type r} [Preorder ι]
variable {J : GrothendieckTopology C}
variable {S : ιᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
variable {P : Cᵒᵖ ⥤ Type q}
variable {x y : (EssentiallySmallFiber.presheafFiber S).obj P}

namespace Stage
namespace Hom

variable {A B D E : Stage.{u, v, q, r, r'} (J := J) S P x y}

section CategoryImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The identity refinement preserves every solved request of a saturation stage. -/
private theorem idSolvedMono (A : Stage.{u, v, q, r, r'} (J := J) S P x y) :
    ∀ ⦃request : A.toSeparatingStage.target.Request J⦄, request ∈ A.solved →
      (OrderedRefinement.id A.diagram).mapRequest request ∈ A.solved := sorry

/-- A composite stage refinement carries every solved source request to a solved final request. -/
private theorem compSolvedMono (f : Hom A B) (g : Hom B D) :
    ∀ ⦃request : A.toSeparatingStage.target.Request J⦄, request ∈ A.solved →
      (f.toRefinement.comp g.toRefinement).mapRequest request ∈ D.solved := sorry

end Implementation

/-- The identity morphism of a saturation stage. -/
noncomputable def id (A : Stage.{u, v, q, r, r'} (J := J) S P x y) : Hom A A where
  toSeparatingStage := SeparatingStage.Hom.id A.toSeparatingStage
  solvedMono := Implementation.idSolvedMono A

/-- Compose two morphisms of saturation stages. -/
noncomputable def comp (f : Hom A B) (g : Hom B D) : Hom A D where
  toSeparatingStage :=
    SeparatingStage.Hom.comp f.toSeparatingStage g.toSeparatingStage
  solvedMono := Implementation.compSolvedMono f g

end CategoryImplementation

/-- Forgetting scheduling from an identity stage morphism gives the identity separating-stage
morphism. -/
@[simp]
theorem id.toSeparatingStage (A : Stage.{u, v, q, r, r'} (J := J) S P x y) :
    (id A).toSeparatingStage = SeparatingStage.Hom.id A.toSeparatingStage := sorry

/-- Forgetting scheduling from a composite stage morphism gives the composite separating-stage
morphism. -/
@[simp]
theorem comp.toSeparatingStage (f : Hom A B) (g : Hom B D) :
    (comp f g).toSeparatingStage =
      SeparatingStage.Hom.comp f.toSeparatingStage g.toSeparatingStage := sorry

/-- The ordered refinement underlying an identity scheduled-stage morphism is the identity
refinement. -/
@[simp]
theorem id.toRefinement (A : Stage.{u, v, q, r, r'} (J := J) S P x y) :
    (id A).toRefinement = OrderedRefinement.id A.diagram := sorry

/-- The ordered refinement underlying a composite scheduled-stage morphism is the composite of
the underlying refinements. -/
@[simp]
theorem comp.toRefinement (f : Hom A B) (g : Hom B D) :
    (comp f g).toRefinement = f.toRefinement.comp g.toRefinement := sorry

/-- Scheduled-stage morphisms are determined by their underlying ordered refinement. -/
@[ext]
theorem ext {f g : Hom A B} (h_refinement : f.toRefinement = g.toRefinement) : f = g := sorry

/-- Mapping a request through an identity stage morphism leaves it unchanged. -/
@[simp]
theorem id.mapRequest
    (A : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (request : A.toSeparatingStage.target.Request J) :
    mapRequest (id A) request = request := sorry

/-- Mapping a request through a composite stage morphism agrees with successive transport. -/
@[simp]
theorem comp.mapRequest (f : Hom A B) (g : Hom B D)
    (request : A.toSeparatingStage.target.Request J) :
    mapRequest (comp f g) request = mapRequest g (mapRequest f request) := sorry

/-- Composing an identity scheduled-stage morphism on the left leaves a morphism unchanged. -/
theorem id_comp (f : Hom A B) : comp (id A) f = f := sorry

/-- Composing an identity scheduled-stage morphism on the right leaves a morphism unchanged. -/
theorem comp_id (f : Hom A B) : comp f (id B) = f := sorry

/-- Composition of scheduled-stage morphisms is associative. -/
theorem comp_assoc (f : Hom A B) (g : Hom B D) (h : Hom D E) :
    comp (comp f g) h = comp f (comp g h) := sorry

end Hom

/-- Scheduled saturation stages and factorized solved-request morphisms form a category. -/
noncomputable instance instCategory :
    Category (Stage.{u, v, q, r, r'} (J := J) S P x y) where
  Hom A B := Hom A B
  id A := Hom.id A
  comp f g := Hom.comp f g
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.comp_assoc

end Stage

/- Data and axiom audit (mathlib 4.32): identity and composition data are explicit. Any
`sorryAx` below is confined to proposition-valued solved-set preservation or category-law
fields. -/

end Stage

end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
