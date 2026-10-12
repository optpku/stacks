/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Equivalence
public import ReasLib.CategoryTheory.Abelian.SerreQuotient
public import stacks_project.Chap110.Proposition_110_77_1_Torsion

/-!
# Serre quotient of modules by S-torsion

The exact localization functor `ModuleCat R ⥤ ModuleCat (Localization S)` descends uniquely
through the Serre quotient by `S`-torsion. Restriction of scalars, followed by the Serre
quotient functor, is the canonical inverse on objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe v u

namespace ModuleCat

variable {R : Type u} [CommRing R] [Small.{v} R]

/-- Localization of modules, bundled as an exact functor. -/
def localizedExactFunctor (S : Submonoid R) :
    ModuleCat.{v} R ⥤ₑ ModuleCat.{v} (Localization S) :=
  ExactFunctor.of (localizedModuleFunctor.{v} S)

/-- The underlying functor of `localizedExactFunctor` is localization of modules. -/
theorem localizedExactFunctor_obj (S : Submonoid R) :
    (localizedExactFunctor S).obj = localizedModuleFunctor.{v} S :=
  sorry

/-- The exact functor induced on the Serre quotient of `S`-torsion modules by localization. -/
def inducedLocalizedFunctor (S : Submonoid R) :
    (isTorsion' S).isoModSerre.Localization ⥤ ModuleCat.{v} (Localization S) :=
  SerreClassLocalization.inducedFunctor (isTorsion' S) (localizedExactFunctor S) le_rfl

/-- Restriction of scalars, then the Serre quotient by `S`-torsion. -/
def quotientRestrictScalars (S : Submonoid R) :
    ModuleCat.{v} (Localization S) ⥤ (isTorsion' S).isoModSerre.Localization :=
  restrictScalars (algebraMap R (Localization S)) ⋙ (isTorsion' S).isoModSerre.Q

/-- The Serre quotient followed by the induced functor recovers localization of modules. -/
def inducedLocalizedFunctor_fac (S : Submonoid R) :
    (isTorsion' S).isoModSerre.Q ⋙ inducedLocalizedFunctor S ≅
      localizedModuleFunctor.{v} S :=
  CategoryTheory.Localization.fac (localizedExactFunctor S).obj
    (((isTorsion' S).isoModSerre_isInvertedBy_iff (localizedExactFunctor S).obj).2 le_rfl)
    (isTorsion' S).isoModSerre.Q

/-- The factorization isomorphism is inverted by its inverse. -/
theorem inducedLocalizedFunctor_fac_hom_inv_id (S : Submonoid R) :
    (inducedLocalizedFunctor_fac S).hom ≫ (inducedLocalizedFunctor_fac S).inv =
      𝟙 ((isTorsion' S).isoModSerre.Q ⋙ inducedLocalizedFunctor S) :=
  sorry

/-- The inverse sends an `S⁻¹R`-module to its restriction of scalars in the Serre quotient. -/
theorem quotientRestrictScalars_obj (S : Submonoid R)
    (N : ModuleCat.{v} (Localization S)) :
    (quotientRestrictScalars S).obj N =
      (isTorsion' S).isoModSerre.Q.obj
        ((restrictScalars (algebraMap R (Localization S))).obj N) :=
  sorry

/-- The induced localization functor on the Serre quotient by `S`-torsion is an equivalence. -/
theorem inducedLocalizedFunctor_isEquivalence (S : Submonoid R) :
    (inducedLocalizedFunctor S).IsEquivalence :=
  sorry

end ModuleCat
