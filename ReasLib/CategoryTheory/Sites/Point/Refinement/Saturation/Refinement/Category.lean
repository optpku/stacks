/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Refinement.Hom

/-!
# The category of unseparated finite-cover refinement stages

This leaf supplies identity, composition, and the forgetful functor for
compatible finite-cover refinement stages.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v q r r' r'' r'''

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation

variable {C : Type u} [Category.{v} C]
variable {ι : Type r} [Preorder ι]
variable {J : GrothendieckTopology C}

namespace RefinementStage

variable {S : ιᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]

namespace Hom

variable {A : RefinementStage.{u, v, q, r, r'} S}
variable {B : RefinementStage.{u, v, q, r, r''} S}
variable {D : RefinementStage.{u, v, q, r, r'''} S}
variable {E : RefinementStage.{u, v, q, r, r'''} S}

/-- The identity morphism of a finite-cover refinement stage. -/
noncomputable def id (A : RefinementStage.{u, v, q, r, r'} S) : Hom A A where
  refinement := OrderedRefinement.id A.diagram
  factorization := IsFactorization.id_right A.toRefinement

/-- Compose compatible morphisms of finite-cover refinement stages. -/
noncomputable def comp (f : Hom A B) (g : Hom B D) : Hom A D where
  refinement := f.toRefinement.comp g.toRefinement
  factorization := IsFactorization.trans f.factorization g.factorization

/-- The ordered refinement underlying an identity refinement-stage morphism is the identity
refinement. -/
@[simp]
theorem id.toRefinement (A : RefinementStage.{u, v, q, r, r'} S) :
    (id A).toRefinement = OrderedRefinement.id A.diagram := sorry

/-- The ordered refinement underlying a composite refinement-stage morphism is the composite of
the underlying refinements. -/
@[simp]
theorem comp.toRefinement (f : Hom A B) (g : Hom B D) :
    (comp f g).toRefinement = f.toRefinement.comp g.toRefinement := sorry

/-- Refinement-stage morphisms are determined by their underlying ordered refinement. -/
@[ext]
theorem ext {f g : Hom A B} (h_refinement : f.toRefinement = g.toRefinement) : f = g := sorry

/-- Mapping through an identity refinement-stage morphism leaves a request unchanged. -/
@[simp]
theorem id.mapRequest (A : RefinementStage.{u, v, q, r, r'} S)
    (request : A.target.Request J) : mapRequest (id A) request = request := sorry

/-- Mapping through a composite refinement-stage morphism agrees with successive transport. -/
@[simp]
theorem comp.mapRequest (f : Hom A B) (g : Hom B D) (request : A.target.Request J) :
    mapRequest (comp f g) request = mapRequest g (mapRequest f request) := sorry

/-- Composing an identity refinement-stage morphism on the left changes no refinement. -/
theorem id_comp (f : Hom A B) : comp (id A) f = f := sorry

/-- Composing an identity refinement-stage morphism on the right changes no refinement. -/
theorem comp_id (f : Hom A B) : comp f (id B) = f := sorry

/-- Composition of compatible refinement-stage morphisms is associative. -/
theorem comp_assoc (f : Hom A B) (g : Hom B D)
    (h : Hom D E) : comp (comp f g) h = comp f (comp g h) := sorry

end Hom

/-- Finite-cover refinement stages and compatible refinements form a category. -/
noncomputable instance instCategory :
    Category (RefinementStage.{u, v, q, r, r'} S) where
  Hom A B := Hom A B
  id A := Hom.id A
  comp f g := Hom.comp f g
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.comp_assoc

namespace Hom

variable {A : RefinementStage.{u, v, q, r, r'} S}
variable {B : RefinementStage.{u, v, q, r, r''} S}
variable {D : RefinementStage.{u, v, q, r, r'''} S}

/-- Forgetting an identity refinement-stage morphism gives the identity target morphism. -/
@[simp]
theorem id.toTarget (A : RefinementStage.{u, v, q, r, r'} S) :
    (id A).toTarget = Target.Hom.id A.target := sorry

/-- Forgetting a composite refinement-stage morphism gives the composite target morphism. -/
@[simp]
theorem comp.toTarget (f : Hom A B) (g : Hom B D) :
    (comp f g).toTarget = Target.Hom.comp f.toTarget g.toTarget := sorry

end Hom

/-- Forget the original-system factorization while retaining each target and its transition
refinement.  This is the canonical bridge into the source-free target-diagram API. -/
noncomputable def forget :
    RefinementStage.{u, v, q, r, r'} S ⥤ Target.{u, v, q, r'} C where
  obj := fun A => A.target
  map := fun f => f.toTarget
  map_id := Hom.id.toTarget
  map_comp := Hom.comp.toTarget

namespace forget

/-- The forgetful functor sends a refinement stage to its packaged target. -/
@[simp]
theorem obj (A : RefinementStage.{u, v, q, r, r'} S) :
    (forget (S := S)).obj A = A.target := sorry

/-- The forgetful functor sends a refinement-stage morphism to its source-free target
refinement. -/
@[simp]
theorem map {A B : RefinementStage.{u, v, q, r, r'} S} (f : Hom A B) :
    (forget (S := S)).map f = f.toTarget := sorry

end forget
end RefinementStage

end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
