/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Target.Basic

/-!
# The category of finite-cover saturation targets

This file owns source-free target refinements, their finite-cover request API,
identity and composition, and the resulting category instance.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v q r r' r'' r''' w'

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation
namespace Target

variable {C : Type u} [Category.{v} C]
variable [LocallySmall.{q} C]
variable {J : GrothendieckTopology C}

/-- A source-free finite-cover refinement between two saturation targets. -/
structure Hom
    (A : Target.{u, v, q, r} C)
    (B : Target.{u, v, q, r'} C) where
  /-- The ordered refinement of the two target systems. -/
  refinement : OrderedRefinement A.diagram B.diagram

namespace Hom

variable {A : Target.{u, v, q, r} C}
variable {B : Target.{u, v, q, r'} C}
variable {D : Target.{u, v, q, r''} C}
variable {E : Target.{u, v, q, r'''} C}

/-- The ordered refinement carried by a target morphism. -/
abbrev toRefinement (f : Hom A B) : OrderedRefinement A.diagram B.diagram :=
  f.refinement

/-- Transport a finite-cover request along a target refinement. -/
noncomputable def mapRequest (f : Hom A B) (request : A.Request J) : B.Request J :=
  f.toRefinement.mapRequest request

namespace mapRequest

/-- A realized finite-cover request remains realized after transport along a target
refinement. -/
theorem isRealized (f : Hom A B) (request : A.Request J) :
    request.is_realized → (f.mapRequest request).is_realized := sorry

end mapRequest

/-- A target refinement realizes all finite-cover requests already present at its source. -/
def realizesAll (f : Hom A B) : Prop :=
  ∀ request : A.Request J, (f.mapRequest request).is_realized

/-- Realizing every target request is finite-cover lifting by the underlying refinement. -/
theorem realizesAll_iff_finiteCoverLifts (f : Hom A B) :
    f.realizesAll (J := J) ↔
      NatTrans.FiniteCoverLifts.{u, v, q, w'}
        (OrderedRefinement.EssentiallySmall.fiberMap f.toRefinement) J := sorry

/-- The identity target refinement. -/
noncomputable def id (A : Target.{u, v, q, r} C) : Hom A A where
  refinement := OrderedRefinement.id A.diagram

/-- Compose source-free target refinements. -/
noncomputable def comp (f : Hom A B) (g : Hom B D) : Hom A D where
  refinement := f.toRefinement.comp g.toRefinement

namespace id

/-- The ordered refinement underlying an identity target morphism is the identity
refinement. -/
@[simp]
theorem toRefinement (A : Target.{u, v, q, r} C) :
    (id A).toRefinement = OrderedRefinement.id A.diagram := sorry

end id

namespace comp

/-- The ordered refinement underlying a composite target morphism is the composite of the
underlying refinements. -/
@[simp]
theorem toRefinement (f : Hom A B) (g : Hom B D) :
    (comp f g).toRefinement = f.toRefinement.comp g.toRefinement := sorry

end comp

/-- Target refinements are determined by their ordered refinement. -/
@[ext]
theorem ext {f g : Hom A B} (h_refinement : f.toRefinement = g.toRefinement) : f = g := sorry

namespace id

/-- Mapping a request through an identity target refinement leaves it unchanged. -/
@[simp]
theorem mapRequest (A : Target.{u, v, q, r} C)
    (request : A.Request J) : Hom.mapRequest (id A) request = request := sorry

end id

namespace comp

/-- Mapping through a composite target refinement agrees with successive transport. -/
@[simp]
theorem mapRequest (f : Hom A B) (g : Hom B D) (request : A.Request J) :
    Hom.mapRequest (comp f g) request =
      Hom.mapRequest g (Hom.mapRequest f request) := sorry

end comp

/-- Composing an identity target refinement on the left leaves a refinement unchanged. -/
theorem id_comp (f : Hom A B) : comp (id A) f = f := sorry

/-- Composing an identity target refinement on the right leaves a refinement unchanged. -/
theorem comp_id (f : Hom A B) : comp f (id B) = f := sorry

/-- Composition of source-free target refinements is associative. -/
theorem comp_assoc (f : Hom A B) (g : Hom B D) (h : Hom D E) :
    comp (comp f g) h = comp f (comp g h) := sorry

end Hom

/-- Saturation targets in one index universe form a category under source-free refinements. -/
noncomputable instance instCategory :
    Category (Target.{u, v, q, r} C) where
  Hom A B := Hom A B
  id A := Hom.id A
  comp f g := Hom.comp f g
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.comp_assoc

end Target
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
