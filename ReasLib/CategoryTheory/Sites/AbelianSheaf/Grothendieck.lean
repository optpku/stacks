module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import ReasLib.CategoryTheory.Abelian.FunctorialInjectives.Grothendieck
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Grothendieck structure on abelian sheaves

This leaf owns the reusable instance chain from the Grothendieck structure on abelian sheaves to
functorial injective embeddings and enough injectives. Consumers do not need to install a local
small model of the site.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.AbelianSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The category of abelian sheaves on a site is Grothendieck abelian in a universe containing
both the objects and morphisms of the site. -/
@[stacks 01DP "Grothendieck-abelian owner"]
noncomputable instance isGrothendieckAbelian :
    IsGrothendieckAbelian.{max u v} (Sheaf J AddCommGrpCat.{max u v}) := sorry

/-- Abelian sheaves on a site admit a functorial choice of monomorphisms into injective objects.
In particular, the category has enough injectives. -/
@[stacks 01DG "topological-space specialization", stacks 01DP]
noncomputable instance hasFunctorialInjectives :
    HasFunctorialInjectives (Sheaf J AddCommGrpCat.{max u v}) :=
  IsGrothendieckAbelian.hasFunctorialInjectives

/-- Abelian sheaves on a site have enough injectives. -/
noncomputable instance enoughInjectives :
    EnoughInjectives (Sheaf J AddCommGrpCat.{max u v}) :=
  CategoryTheory.IsGrothendieckAbelian.enoughInjectives

end CategoryTheory.AbelianSheaf
