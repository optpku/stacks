/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Sheaf.AffineBasis
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.Abelian
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.Modules.DerivedSections

variable (A : Type u) [CommRing A] (Y : Scheme.{u})

/-- The identity presentation change from topological sheaves to sheaves
on the opens site. It leaves every section and restriction map unchanged. -/
noncomputable def asSiteSheaf :
    TopCat.Sheaf (ModuleCat.{u} A) Y.toTopCat ⥤
      Sheaf (Opens.grothendieckTopology Y.toTopCat) (ModuleCat.{u} A) where
  obj M := M
  map f := f

/-- The identity presentation change is additive. -/
instance asSiteSheaf_additive : (asSiteSheaf A Y).Additive where
  map_add := by intros; rfl

/-- Canonical universe lifting of the actual A-module sheaves. -/
noncomputable def liftSheaf :
    TopCat.Sheaf (ModuleCat.{u} A) Y.toTopCat ⥤
      Sheaf (Opens.grothendieckTopology Y.toTopCat) (ModuleCat.{u + 1} A) :=
  asSiteSheaf A Y ⋙ sheafCompose _ (ModuleCat.uliftFunctor.{u + 1, u} A)

/-- Universe lifting preserves addition of the actual sheaf maps. -/
instance liftSheaf_additive : (liftSheaf A Y).Additive := sorry

variable [HasSheafify (Opens.grothendieckTopology Y.toTopCat) (ModuleCat.{u + 1} A)]

/-- Use the canonical derived category of A-module sheaves, not the
derived category of their underlying abelian groups. -/
noncomputable instance sheafDerivedCategory :
    HasDerivedCategory (Sheaf (Opens.grothendieckTopology Y.toTopCat) (ModuleCat.{u + 1} A)) :=
  HasDerivedCategory.standard _

variable [HasGlobalSectionsFunctor (Opens.grothendieckTopology Y.toTopCat) (ModuleCat.{u + 1} A)]

/-- Global sections of A-module sheaves are additive. The actual functor
is the constant-sheaf right adjoint; it retains the A-module structure. -/
noncomputable instance sections_additive :
    (Sheaf.Γ (Opens.grothendieckTopology Y.toTopCat) (ModuleCat.{u + 1} A)).Additive := sorry

variable [IsGrothendieckAbelian
  (Sheaf (Opens.grothendieckTopology Y.toTopCat) (ModuleCat.{u + 1} A))]

/-- Genuine derived global sections of a specified nonnegative complex of
A-module sheaves, with canonical universe lifting and degree extension. -/
noncomputable def ofComplex
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u} A) Y.toTopCat) ℕ) :
    DerivedCategory (ModuleCat.{u + 1} A) :=
  (Functor.RightDerived.Cochain.functor
    (Sheaf.Γ (Opens.grothendieckTopology Y.toTopCat) (ModuleCat.{u + 1} A))).obj
      (DerivedCategory.Q.obj
        ((ComplexShape.embeddingUpNat.extendFunctor _).obj
          (((liftSheaf A Y).mapHomologicalComplex (ComplexShape.up ℕ)).obj K)))

end AlgebraicGeometry.Scheme.Modules.DerivedSections
