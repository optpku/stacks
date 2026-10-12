/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived
public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Basic

/-!
# Forgetting the action on derived differential graded modules

The functor which forgets a differential graded algebra action first descends to homotopy
categories and then through the two quasi-isomorphism localizations.  The resulting functor to
the ordinary derived category is conservative.  It also reflects source-defined derived values;
this is the reusable mechanism behind enriched derived-Hom constructions whose existence is
checked on underlying complexes.
-/

@[expose] public section

noncomputable section

universe u v w z

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace DifferentialGradedModule.Derived

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra R)

/-- The homotopy-level forgetful functor followed by ordinary localization inverts
quasi-isomorphisms of differential graded modules. -/
theorem quasiIso_isInvertedBy_forgetQh :
    (DifferentialGradedModule.quasiIso.{u, v} A).IsInvertedBy
      (DifferentialGradedModule.Homotopy.forget A ⋙
        DerivedCategory.Qh (C := ModuleCat.{v} R)) := sorry

/-- Forget the differential graded algebra action after passing to derived categories. -/
@[stacks 09LK "forgetful functor from derived DG modules to derived complexes"]
noncomputable def forget :
    Category.{u, v} A ⥤ DerivedCategory (ModuleCat.{v} R) :=
  Localization.lift
    (DifferentialGradedModule.Homotopy.forget A ⋙
      DerivedCategory.Qh (C := ModuleCat.{v} R))
    (quasiIso_isInvertedBy_forgetQh A) (Q A)

/-- The derived DG-module forgetful functor is additive. -/
@[stacks 09LK "additivity of the derived DG-module forgetful functor"]
noncomputable instance forget_additive :
    (forget A).Additive := sorry

/-- The derived DG-module forgetful functor is linear over the ground ring. -/
@[stacks 09LK "linearity of the derived DG-module forgetful functor"]
noncomputable instance forget_linear :
    (forget A).Linear R := sorry

/-- The derived forgetful functor is characterized by its canonical factorization through the
DG-module localization. -/
noncomputable def forgetFactors :
    Q.{u, v} A ⋙ forget A ≅
      DifferentialGradedModule.Homotopy.forget A ⋙
        DerivedCategory.Qh (C := ModuleCat.{v} R) :=
  Localization.fac
    (DifferentialGradedModule.Homotopy.forget A ⋙
      DerivedCategory.Qh (C := ModuleCat.{v} R))
    (quasiIso_isInvertedBy_forgetQh A) (Q A)

/-- Forgetting the differential graded algebra action detects isomorphisms in the derived
category. -/
@[stacks 09LK "derived DG-module forgetful functor detects isomorphisms"]
instance forget_reflectsIsomorphisms : (forget.{u, v} A).ReflectsIsomorphisms := sorry

variable {𝒞 : Type w} [_root_.CategoryTheory.Category.{z} 𝒞]

/-- A right-derived value of a DG-module-valued functor is source-defined whenever its
underlying ordinary derived-complex value is source-defined. -/
instance rightDerivedDefinedAt_of_forget
    (F : 𝒞 ⥤ Category.{u, v} A) (S : MorphismProperty 𝒞) (X : 𝒞)
    [Functor.RightDerived.DefinedAt (F ⋙ forget A) S X] :
    Functor.RightDerived.DefinedAt F S X := sorry

/-- A left-derived value of a DG-module-valued functor is source-defined whenever its
underlying ordinary derived-complex value is source-defined. -/
instance leftDerivedDefinedAt_of_forget
    (F : 𝒞 ⥤ Category.{u, v} A) (S : MorphismProperty 𝒞) (X : 𝒞)
    [Functor.LeftDerived.DefinedAt (F ⋙ forget A) S X] :
    Functor.LeftDerived.DefinedAt F S X := sorry

/-- Everywhere-definedness of a right-derived DG-module-valued functor can be checked after
forgetting the differential graded algebra action. -/
@[stacks 09LK "underlying criterion for enriched right-derived functors"]
instance rightDerivedEverywhereDefined_of_forget
    (F : 𝒞 ⥤ Category.{u, v} A) (S : MorphismProperty 𝒞)
    [Functor.RightDerived.EverywhereDefined (F ⋙ forget A) S] :
    Functor.RightDerived.EverywhereDefined F S := sorry

/-- Everywhere-definedness of a left-derived DG-module-valued functor can be checked after
forgetting the differential graded algebra action. -/
instance leftDerivedEverywhereDefined_of_forget
    (F : 𝒞 ⥤ Category.{u, v} A) (S : MorphismProperty 𝒞)
    [Functor.LeftDerived.EverywhereDefined (F ⋙ forget A) S] :
    Functor.LeftDerived.EverywhereDefined F S := sorry

#synth (forget A).Additive
#synth Functor.Linear R (forget A)

end DifferentialGradedModule.Derived
