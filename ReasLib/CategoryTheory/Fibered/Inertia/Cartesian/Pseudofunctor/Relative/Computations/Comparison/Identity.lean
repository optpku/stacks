module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Relative.Computations.Action

/-!
# Identity comparison computations for fibred relative inertia
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace FiberedCategoryOver.RelativeInertia.pseudoComma

variable {C : Type u} [Category.{v} C]

/-- The identity comparison of fibred relative inertia is the canonical lift
of its based identity comparison. -/
@[simp]
theorem pseudofunctor.mapId
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))) :
    (pseudofunctor C).mapId S =
      FiberedCategoryOver.BasedFunctorIso.lift
        ((basedPseudofunctor C).mapId S) := sorry

/-- The forward fibred relative-inertia identity comparison forgets to the
underlying based comparison cell. -/
@[simp]
theorem pseudofunctor.mapId.hom.toBasedNatTrans
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))) :
    FiberedCategoryOver.toBasedNatTrans
        ((pseudofunctor C).mapId S).hom =
      ((basedPseudofunctor C).mapId S).hom := sorry

/-- The inverse fibred relative-inertia identity comparison forgets to the
underlying based comparison cell. -/
@[simp]
theorem pseudofunctor.mapId.inv.toBasedNatTrans
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))) :
    FiberedCategoryOver.toBasedNatTrans
        ((pseudofunctor C).mapId S).inv =
      ((basedPseudofunctor C).mapId S).inv := sorry

/-- The forward identity comparison component is the corresponding component
of the based relative-inertia pseudofunctor. -/
@[simp]
theorem pseudofunctor.mapId.hom.app
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C)))
    (A : ((pseudofunctor C).obj S).total) :
    (FiberedCategoryOver.toNatTrans
        ((pseudofunctor C).mapId S).hom).app A =
      ((basedPseudofunctor C).mapId S).hom.toNatTrans.app A := sorry

/-- The inverse identity comparison component is the corresponding component
of the based relative-inertia pseudofunctor. -/
@[simp]
theorem pseudofunctor.mapId.inv.app
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C)))
    (A : ((pseudofunctor C).obj S).total) :
    (FiberedCategoryOver.toNatTrans
        ((pseudofunctor C).mapId S).inv).app A =
      ((basedPseudofunctor C).mapId S).inv.toNatTrans.app A := sorry

/-- Every forward component of the packaged fibred relative-inertia identity comparison is
vertical over the identity base arrow. -/
theorem pseudofunctor.mapId.hom.app.isHomLift
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C)))
    (A : ((pseudofunctor C).obj S).total) :
    (FiberedCategoryOver.relativeInertia S.hom).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.relativeInertia S.hom).p.obj A))
      ((FiberedCategoryOver.toNatTrans
        ((pseudofunctor C).mapId S).hom).app A) := sorry

/-- Every inverse component of the packaged fibred relative-inertia identity comparison is
vertical over the identity base arrow. -/
theorem pseudofunctor.mapId.inv.app.isHomLift
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C)))
    (A : ((pseudofunctor C).obj S).total) :
    (FiberedCategoryOver.relativeInertia S.hom).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.relativeInertia S.hom).p.obj A))
      ((FiberedCategoryOver.toNatTrans
        ((pseudofunctor C).mapId S).inv).app A) := sorry

/-- The ambient arrow underlying a forward identity-comparison component is
the identity of the underlying relative-inertia object. -/
@[simp]
theorem pseudofunctor.mapId.hom.app.underlying
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C)))
    (A : ((pseudofunctor C).obj S).total) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.toNatTrans
          ((pseudofunctor C).mapId S).hom).app A) =
      𝟙 A.obj := sorry

/-- The ambient arrow underlying an inverse identity-comparison component is
the identity of the underlying relative-inertia object. -/
@[simp]
theorem pseudofunctor.mapId.inv.app.underlying
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C)))
    (A : ((pseudofunctor C).obj S).total) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.toNatTrans
          ((pseudofunctor C).mapId S).inv).app A) =
      𝟙 A.obj := sorry

end FiberedCategoryOver.RelativeInertia.pseudoComma

end CategoryTheory
