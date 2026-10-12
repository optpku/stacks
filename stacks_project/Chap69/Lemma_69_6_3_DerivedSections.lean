/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import stacks_project.Chap69.Definition_69_6_2_ExtensionByZero

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
  preadditiveYoneda.flip.obj (op (constantIntegerSheaf X))

/-- Evaluating global sections on an abelian étale sheaf yields `Hom(ℤ̲, F)`. -/
theorem globalSections_obj (X : AlgebraicSpace S)
    [Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    (globalSections X).obj F =
      (preadditiveYoneda.obj F).obj (op (constantIntegerSheaf X)) :=
  sorry

/-- Applying a morphism of abelian étale sheaves on global sections is postcomposition
on `Hom(ℤ̲, -)`. -/
theorem globalSections_map (X : AlgebraicSpace S)
    [Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    (globalSections X).map φ =
      (preadditiveYoneda.map φ).app (op (constantIntegerSheaf X)) :=
  sorry

/-- Global sections of abelian étale sheaves are additive. -/
instance globalSections_additive (X : AlgebraicSpace S)
    [Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})] :
    (globalSections X).Additive :=
  sorry

/-- On a site admitting a global-sections right adjoint to the constant sheaf, `Hom(ℤ̲, -)`
recovers `Sheaf.Γ`. -/
theorem globalSections_isomorphic_gamma (X : AlgebraicSpace S)
    [HasWeakSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasGlobalSectionsFunctor (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})] :
    IsIsomorphic (globalSections X) (Sheaf.Γ (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
