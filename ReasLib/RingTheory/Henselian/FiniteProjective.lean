/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.RingTheory.Henselian
public import ReasLib.Algebra.Category.ModuleCat.FiniteProjective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite projective modules over henselian pairs

Reduction modulo a henselian ideal induces a functor between the finite-projective module
categories and a bijection on their isomorphism classes.  The functor is the canonical scalar
extension functor restricted by `ObjectProperty.lift`; only its preservation and henselian
comparison laws are deferred.

@stack 0D4A
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

variable {R : Type u} [CommRing R]

/-- Scalar extension along `R → R ⧸ I` preserves finite projective modules. -/
@[stacks 0D4A "finite-projective preservation under quotient base change"]
theorem finiteProjectiveReduction_property (I : Ideal R)
    (P : ModuleCat.FiniteProjective R) :
    ModuleCat.finiteProjective (R ⧸ I)
      ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj P.obj) := sorry

/-- Reduction modulo `I`, as the scalar-extension functor on finite projective modules. -/
@[stacks 0D4A "finite-projective reduction functor"]
noncomputable def finiteProjectiveReductionFunctor (I : Ideal R) :
    ModuleCat.FiniteProjective R ⥤ ModuleCat.FiniteProjective (R ⧸ I) :=
  (ModuleCat.finiteProjective (R ⧸ I)).lift
    ((ModuleCat.finiteProjective R).ι ⋙ ModuleCat.extendScalars (Ideal.Quotient.mk I))
    (fun P ↦ finiteProjectiveReduction_property I P)

variable (I : Ideal R) [HenselianRing R I]

/-- Lemma 15.13.1 (0D4A) (1): reduction modulo `I` induces a bijection on isomorphism
classes of finite projective modules over a henselian pair `(R, I)`. -/
@[stacks 0D4A "(1), finite projective reduction is bijective on isomorphism classes"]
theorem finiteProjectiveReduction_isoClasses_bijective_of_henselianRing :
    Function.Bijective
      (isomorphismClasses.map (finiteProjectiveReductionFunctor I).toCatHom) := sorry

/-- Lemma 15.13.1 (0D4A) (2): every finite projective `R ⧸ I`-module lifts to a finite
projective `R`-module over a henselian pair. -/
@[stacks 0D4A "(2), finite projective modules lift across henselian quotients"]
theorem exists_finiteProjective_lift_of_henselianRing
    (Pbar : ModuleCat.FiniteProjective (R ⧸ I)) :
    ∃ P : ModuleCat.FiniteProjective R,
      Nonempty ((finiteProjectiveReductionFunctor I).obj P ≅ Pbar) := sorry

/-- Reduction modulo a henselian ideal reflects isomorphisms between finite projective
modules. -/
@[stacks 0D4A "finite-projective reduction reflects isomorphism classes"]
theorem finiteProjective_iso_of_quotient_iso_of_henselianRing
    {P₁ P₂ : ModuleCat.FiniteProjective R}
    (h : Nonempty ((finiteProjectiveReductionFunctor I).obj P₁ ≅
      (finiteProjectiveReductionFunctor I).obj P₂)) :
    Nonempty (P₁ ≅ P₂) := sorry
