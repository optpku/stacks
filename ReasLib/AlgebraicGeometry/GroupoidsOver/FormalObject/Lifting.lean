module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Functor.Category
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormallySmoothOnObjects
public import ReasLib.AlgebraicGeometry.FormalSpace.AdicDiagram
public import ReasLib.RingTheory.Completion.LocalRing

/-!
# Lifting maximal-adic systems in groupoid fibrations

Formal smoothness on objects extends a specified residue-field lift to a
compatible system over the maximal-adic quotient diagram.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidsOver.FormalObject

/-- A formally smooth morphism on objects lifts a maximal-adic system from a
specified residue-field object, with a vertical isomorphism to that object
compatible with the prescribed image isomorphism. -/
theorem exists_lift_stageOne
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X Y : GroupoidsOver S}
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]
    (toS : Spec (CommRingCat.of R) ⟶ S)
    (hres : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R))) ≫ toS))
    (F : X ⟶ Y) [AlgebraicGeometry.Groupoids.Hom.FormallySmoothOnObjects F]
    (η : ℕ ⥤ Y.total) (hη : η ⋙ Y.p = AdicPresentation.diagram toS (maximalIdeal R))
    (ξ1 : X.total) (hξ1 : X.p.obj ξ1 = (AdicPresentation.diagram toS (maximalIdeal R)).obj 0)
    (e : (FiberedCategoryOver.Groupoids.toFunctor F).obj ξ1 ≅ η.obj 0)
    (he : Y.p.IsHomLift (𝟙 ((AdicPresentation.diagram toS (maximalIdeal R)).obj 0)) e.hom) :
    ∃ ξ : ℕ ⥤ X.total, ξ ⋙ X.p = AdicPresentation.diagram toS (maximalIdeal R) ∧
      ∃ (e0 : ξ.obj 0 ≅ ξ1)
        (α : ξ ⋙ FiberedCategoryOver.Groupoids.toFunctor F ≅ η),
        X.p.IsHomLift (𝟙 ((AdicPresentation.diagram toS (maximalIdeal R)).obj 0)) e0.hom ∧
          (∀ n, Y.p.IsHomLift (𝟙 ((AdicPresentation.diagram toS (maximalIdeal R)).obj n))
            (α.hom.app n)) ∧
          α.hom.app 0 = (FiberedCategoryOver.Groupoids.toFunctor F).map e0.hom ≫ e.hom :=
  sorry

/-- A formally smooth morphism on objects lifts a maximal-adic system over a
Noetherian complete local ring from a specified residue-field lift, together
with a natural isomorphism whose components lie over the identity of each
quotient spectrum. -/
theorem exists_lift
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X Y : GroupoidsOver S}
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]
    (toS : Spec (CommRingCat.of R) ⟶ S)
    (hres : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R))) ≫ toS))
    (F : X ⟶ Y) [AlgebraicGeometry.Groupoids.Hom.FormallySmoothOnObjects F]
    (η : ℕ ⥤ Y.total) (hη : η ⋙ Y.p = AdicPresentation.diagram toS (maximalIdeal R))
    (ξ1 : X.total) (hξ1 : X.p.obj ξ1 = (AdicPresentation.diagram toS (maximalIdeal R)).obj 0)
    (e : (FiberedCategoryOver.Groupoids.toFunctor F).obj ξ1 ≅ η.obj 0)
    (he : Y.p.IsHomLift (𝟙 ((AdicPresentation.diagram toS (maximalIdeal R)).obj 0)) e.hom) :
    ∃ ξ : ℕ ⥤ X.total, ξ ⋙ X.p = AdicPresentation.diagram toS (maximalIdeal R) ∧
      ∃ α : ξ ⋙ FiberedCategoryOver.Groupoids.toFunctor F ≅ η,
        ∀ n, Y.p.IsHomLift (𝟙 ((AdicPresentation.diagram toS (maximalIdeal R)).obj n))
          (α.hom.app n) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.FormalObject
