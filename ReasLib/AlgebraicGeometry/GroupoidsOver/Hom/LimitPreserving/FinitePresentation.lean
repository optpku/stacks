module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Hom.LimitPreserving
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreservingOnObjects.FinitePresentation

/-!
# Limit-preserving morphisms and finite presentation

For morphisms of categories fibred in groupoids representable by algebraic
spaces, limit preservation, limit preservation on objects, and local finite
presentation are equivalent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace LimitPreserving

/-- A 1-morphism of categories fibred in groupoids that is representable by
algebraic spaces is limit preserving if and only if it is limit preserving on
objects. -/
theorem iff_limitPreservingOnObjects {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) (hp : relativelyRepresentableByAlgebraicSpaces p) :
    LimitPreserving p ↔ LimitPreservingOnObjects p := sorry

/-- A 1-morphism of categories fibred in groupoids that is representable by
algebraic spaces is limit preserving if and only if it is locally of finite
presentation. -/
theorem iff_locallyOfFinitePresentation {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) (hp : relativelyRepresentableByAlgebraicSpaces p) :
    LimitPreserving p ↔ LocallyOfFinitePresentation p :=
  (iff_limitPreservingOnObjects p hp).trans
    (LimitPreservingOnObjects.iff_locallyOfFinitePresentation p hp)

/-- For a 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf`
representable by algebraic spaces, limit preservation, limit preservation on
objects, and local finite presentation are equivalent. -/
theorem tfae {S : Scheme.{u}} {X Y : GroupoidsOver S} (p : X ⟶ Y)
    (hp : relativelyRepresentableByAlgebraicSpaces p) :
    List.TFAE [LimitPreserving p, LimitPreservingOnObjects p,
      LocallyOfFinitePresentation p] :=
  List.tfae_cons_cons.mpr ⟨iff_limitPreservingOnObjects p hp,
    List.tfae_cons_cons.mpr
      ⟨LimitPreservingOnObjects.iff_locallyOfFinitePresentation p hp,
        List.tfae_singleton _⟩⟩

/-- A 1-morphism of categories fibred in groupoids that is representable by
algebraic spaces and limit preserving on objects is limit preserving. -/
theorem of_limitPreservingOnObjects {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) (hp : relativelyRepresentableByAlgebraicSpaces p)
    [LimitPreservingOnObjects p] :
    LimitPreserving p :=
  (iff_limitPreservingOnObjects p hp).mpr inferInstance

/-- A 1-morphism of categories fibred in groupoids that is locally of finite
presentation is limit preserving. -/
instance of_locallyOfFinitePresentation {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) [LocallyOfFinitePresentation p] :
    LimitPreserving p :=
  (iff_locallyOfFinitePresentation p
    (LocallyOfFinitePresentation.relativelyRepresentable p)).mpr inferInstance

end LimitPreserving

end AlgebraicGeometry.Groupoids.Hom
