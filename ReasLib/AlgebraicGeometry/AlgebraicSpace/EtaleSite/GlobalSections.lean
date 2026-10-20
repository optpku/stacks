module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.ExtensionByZero

/-!
# Global sections of abelian étale sheaves on algebraic spaces

Global sections of an abelian sheaf on `X_étale` are realized as
`Hom(ℤ̲, -)` in `Ab(X_étale)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Global sections of abelian sheaves on the small étale site of an algebraic space,
realized as `Hom(ℤ̲, -)` in `Ab(X_étale)`. -/
noncomputable def globalSections (X : AlgebraicSpace S)
    [Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})] :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  preadditiveYoneda.flip.obj (op (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology X)))

/-- Evaluating global sections on an abelian étale sheaf yields `Hom(ℤ̲, F)`. -/
theorem globalSections_obj (X : AlgebraicSpace S)
    [Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    (globalSections X).obj F =
      (preadditiveYoneda.obj F).obj (op (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology X))) :=
  rfl

/-- Applying a morphism of abelian étale sheaves on global sections is postcomposition
on `Hom(ℤ̲, -)`. -/
theorem globalSections_map (X : AlgebraicSpace S)
    [Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    (globalSections X).map φ =
      (preadditiveYoneda.map φ).app (op (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology X))) :=
  rfl

/-- Global sections of abelian étale sheaves are additive. -/
instance globalSections_additive (X : AlgebraicSpace S)
    [Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})] :
    (globalSections X).Additive :=
  { map_add := by
      intro F G f g
      apply AddCommGrpCat.ext
      intro a
      change a ≫ (f + g) = a ≫ f + a ≫ g
      simp only [Preadditive.comp_add] }

/-- On a site admitting a global-sections right adjoint to the constant sheaf, `Hom(ℤ̲, -)`
recovers `Sheaf.Γ`. -/
theorem globalSections_isomorphic_gamma (X : AlgebraicSpace S)
    [HasWeakSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasGlobalSectionsFunctor (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})] :
    IsIsomorphic (globalSections X) (Sheaf.Γ (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
