module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreservingOnObjects
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property

/-!
# Limit preserving on objects versus locally of finite presentation

A morphism of groupoid fibrations representable by algebraic spaces is limit
preserving on objects if and only if it is locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace LimitPreservingOnObjects

/-- A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces is limit preserving on objects if and only if
it is locally of finite presentation. -/
theorem iff_locallyOfFinitePresentation {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) (hp : relativelyRepresentableByAlgebraicSpaces p) :
    LimitPreservingOnObjects p ↔ LocallyOfFinitePresentation p :=
  sorry

/-- A 1-morphism of categories fibred in groupoids that is locally of finite
presentation is limit preserving on objects. -/
instance of_locallyOfFinitePresentation {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) [LocallyOfFinitePresentation p] :
    LimitPreservingOnObjects p :=
  (iff_locallyOfFinitePresentation p
    (LocallyOfFinitePresentation.relativelyRepresentable p)).mpr inferInstance

/-- A 1-morphism of categories fibred in groupoids that is representable by
algebraic spaces is limit preserving on objects if and only if every
scheme-slice representing morphism is locally of finite presentation. -/
theorem iff_has {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) (hp : relativelyRepresentableByAlgebraicSpaces p) :
    LimitPreservingOnObjects p ↔
      has (@AlgebraicSpace.LocallyOfFinitePresentation S) p := by
  refine (iff_locallyOfFinitePresentation p hp).trans ?_
  exact ⟨fun h => h.of_represents, fun h => ⟨hp, h⟩⟩

end LimitPreservingOnObjects

namespace LocallyOfFinitePresentation

/-- A 1-morphism of categories fibred in groupoids that is representable by
algebraic spaces and limit preserving on objects is locally of finite
presentation. -/
theorem of_limitPreservingOnObjects {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) (hp : relativelyRepresentableByAlgebraicSpaces p)
    [LimitPreservingOnObjects p] :
    LocallyOfFinitePresentation p :=
  (LimitPreservingOnObjects.iff_locallyOfFinitePresentation p hp).mp inferInstance

end LocallyOfFinitePresentation

end AlgebraicGeometry.Groupoids.Hom
