/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Functor.OfSequence
public import ReasLib.Algebra.Category.ModuleCat.IdealPower.Functor

/-!
# Ideal-power quotients of module sheaves

Objectwise exact-power quotients are sheafified here, together with their
inverse system and canonical map to its inverse limit.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v w

namespace CategoryTheory.Sheaf.IdealPower

open Ideal.PowerQuotient

variable {C : Type u} [Category.{v} C] {R : Type w} [CommRing R]
variable {J : GrothendieckTopology C} [HasWeakSheafify J (ModuleCat.{w} R)]

/-- The sheaf `F / I ^ n F`, obtained by sheafifying objectwise exact-power quotients. -/
def quotient (I : Ideal R) (F : Sheaf J (ModuleCat.{w} R)) (n : ℕ) :
    Sheaf J (ModuleCat.{w} R) :=
  (presheafToSheaf J (ModuleCat.{w} R)).obj (F.obj ⋙ stageFunctor I n)

/-- Objectwise projection of a module sheaf onto its exact-power quotient presheaf. -/
def presheafProjection (I : Ideal R) (F : Sheaf J (ModuleCat.{w} R)) (n : ℕ) :
    F.obj ⟶ F.obj ⋙ stageFunctor I n where
  app X := stageProjection I n (F.obj.obj X)
  naturality := sorry

/-- The canonical sheaf morphism `F ⟶ F / I ^ n F`. -/
def projection (I : Ideal R) (F : Sheaf J (ModuleCat.{w} R)) (n : ℕ) :
    F ⟶ quotient I F n :=
  Sheaf.homEquiv.symm
    (presheafProjection I F n ≫ toSheafify J (F.obj ⋙ stageFunctor I n))

/-- The sheafified transition `(F / I ^ (n + 1) F) ⟶ (F / I ^ n F)`. -/
def step (I : Ideal R) (F : Sheaf J (ModuleCat.{w} R)) (n : ℕ) :
    quotient I F (n + 1) ⟶ quotient I F n :=
  (presheafToSheaf J (ModuleCat.{w} R)).map
    (Functor.whiskerLeft F.obj (stageStepNatTrans I n))

/-- Projection to stage `n` factors through the sheafified successor transition. -/
theorem projection_comp_step (I : Ideal R) (F : Sheaf J (ModuleCat.{w} R)) (n : ℕ) :
    projection I F (n + 1) ≫ step I F n = projection I F n := sorry

/-- The inverse system `n ↦ F / I ^ n F` of sheaves of `R`-modules. -/
def system (I : Ideal R) (F : Sheaf J (ModuleCat.{w} R)) :
    ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{w} R) :=
  Functor.ofOpSequence (step I F)

/-- The inverse system evaluates at `n` to the sheafified exact-power quotient. -/
theorem system_obj (I : Ideal R) (F : Sheaf J (ModuleCat.{w} R)) (n : ℕ) :
    (system I F).obj (op n) = quotient I F n := sorry

/-- The cone of canonical projections from `F` to its exact-power quotient tower. -/
def toLimitCone (I : Ideal R) (F : Sheaf J (ModuleCat.{w} R)) :
    Cone (system I F) where
  pt := F
  π :=
    { app n := projection I F n.unop
      naturality := sorry }

/-- The canonical morphism `F ⟶ lim n, F / I ^ n F`. -/
def toLimit (I : Ideal R) (F : Sheaf J (ModuleCat.{w} R)) :
    F ⟶ limit (system I F) :=
  limit.lift (system I F) (toLimitCone I F)

/-- The canonical map to the inverse limit projects to the stage-`n` quotient. -/
theorem toLimit_π (I : Ideal R) (F : Sheaf J (ModuleCat.{w} R)) (n : ℕ) :
    toLimit I F ≫ limit.π (system I F) (op n) = projection I F n := sorry

end CategoryTheory.Sheaf.IdealPower
