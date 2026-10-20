module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Termwise.Minus
public import ReasLib.LinearAlgebra.QuotientByIdeal.QuotientRing
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lifting Bounded-Above Acyclic Complexes Modulo an Ideal

This file packages the module-level quotient comparison and the bounded-above acyclic lifting
criterion used by Lemma 15.76.1.  The source condition on direct summands is kept explicit in the
main theorem; retract-stable object properties have a separate convenience specialization.

@stack 0BC9
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace ModuleCat.ModIdeal

variable {R : Type u} [CommRing R]

/-- The canonical module-level identification of extension to `R ⧸ I` with quotienting by
`I • M`. -/
@[stacks 0BC9 "module reduction as extension of scalars"]
noncomputable def extensionIso (I : Ideal R) (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj M ≅
      ModuleCat.of (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) :=
  (Ideal.Quotient.tensorModuleEquiv I M).toModuleIso

/-- The module reduction comparison sends a pure tensor to the corresponding quotient class. -/
@[simp]
theorem extensionIso_hom_tmul (I : Ideal R) (M : ModuleCat.{u} R)
    (r : R ⧸ I) (x : M) :
    (extensionIso I M).hom.hom (r ⊗ₜ[R] x) =
      r • (Submodule.Quotient.mk x : M ⧸ I • (⊤ : Submodule R M)) := sorry

/-- Conjugating scalar extension by the quotient comparisons gives the canonical map of modules
modulo `I`. -/
theorem extensionIso_naturality (I : Ideal R) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (extensionIso I M).inv ≫
        (ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f ≫
        (extensionIso I N).hom =
      ModuleCat.ofHom (LinearMap.IdealQuotient.map f.hom I) := sorry

/-- Surjectivity after scalar extension to `R ⧸ I` is equivalent to surjectivity of the canonical
map between the quotient modules. -/
theorem extension_map_surjective_iff (I : Ideal R) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    Function.Surjective
        (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f).hom) ↔
      Function.Surjective (LinearMap.IdealQuotient.map f.hom I) := sorry

end ModuleCat.ModIdeal

namespace CategoryTheory.ObjectProperty

variable {R : Type u} [CommRing R]

/-- A source-faithful direct-summand condition on an object property of modules. -/
@[stacks 0BC9 "term property closed under complements"]
def IsClosedUnderComplement (P : ObjectProperty (ModuleCat.{u} R)) : Prop :=
  ∀ ⦃P₁ P₂ : ModuleCat.{u} R⦄, P P₁ → P (P₁ ⊞ P₂) → P P₂

/-- Retract stability implies the one-sided direct-summand condition used in Lemma 15.76.1. -/
theorem isClosedUnderComplement_of_isStableUnderRetracts
    (P : ObjectProperty (ModuleCat.{u} R)) [P.IsStableUnderRetracts] :
    P.IsClosedUnderComplement := sorry

/-- The kernel of a surjection onto a projective member of `P` remains in `P` when `P` is closed
under complementary direct summands. -/
theorem kernel_mem_of_surjective_to_projective
    (P : ObjectProperty (ModuleCat.{u} R))
    (hprojective : ∀ ⦃Q : ModuleCat.{u} R⦄, P Q → Projective Q)
    (hsummand : P.IsClosedUnderComplement) {Q Z : ModuleCat.{u} R} (f : Q ⟶ Z)
    (hQ : P Q) (hZ : P Z) (hsurj : Function.Surjective f.hom) :
    P (kernel f) := sorry

end CategoryTheory.ObjectProperty

namespace CochainComplex.Minus.TermsIn

variable {R : Type u} [CommRing R]

/-- Every term of a bounded-above complex in the image of reduction modulo `I` has a lift in the
original object property. -/
theorem existsTermLiftModIdeal (I : Ideal R)
    (P : ObjectProperty (ModuleCat.{u} R))
    (E : CochainComplex.Minus.TermsIn
      (P.map (ModuleCat.extendScalars (Ideal.Quotient.mk I)))) (n : ℤ) :
    ∃ Q : ModuleCat.{u} R, P Q ∧
      Nonempty ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj Q ≅
        (E : CochainComplex (ModuleCat.{u} (R ⧸ I)) ℤ).X n) := sorry

/-- Lemma 15.76.1: every bounded-above acyclic complex modulo `I` whose terms lift from a
projective class closed under complementary direct summands has a bounded-above acyclic lift over
the original ring. -/
@[stacks 0BC9 "bounded-above acyclic lifting modulo an ideal"]
theorem existsAcyclicLiftModIdeal (I : Ideal R)
    (P : ObjectProperty (ModuleCat.{u} R))
    (hprojective : ∀ ⦃Q : ModuleCat.{u} R⦄, P Q → Projective Q)
    (hsummand : P.IsClosedUnderComplement)
    (hsurj : ∀ ⦃Q₁ Q₂ : ModuleCat.{u} R⦄ (f : Q₁ ⟶ Q₂),
      P Q₁ → P Q₂ →
        Function.Surjective (LinearMap.IdealQuotient.map f.hom I) →
        Function.Surjective f.hom)
    (E : CochainComplex.Minus.TermsIn
      (P.map (ModuleCat.extendScalars (Ideal.Quotient.mk I))))
    (hacyclic :
      (E : CochainComplex (ModuleCat.{u} (R ⧸ I)) ℤ).Acyclic) :
    ∃ (Q : CochainComplex.Minus.TermsIn P)
      (e :
        ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
            (Q : CochainComplex (ModuleCat.{u} R) ℤ) ≅
          (E : CochainComplex (ModuleCat.{u} (R ⧸ I)) ℤ)),
      (Q : CochainComplex (ModuleCat.{u} R) ℤ).Acyclic := sorry

/-- Retract-stable specialization of bounded-above acyclic lifting modulo an ideal. -/
theorem existsAcyclicLiftModIdeal_of_retracts (I : Ideal R)
    (P : ObjectProperty (ModuleCat.{u} R))
    (hprojective : ∀ ⦃Q : ModuleCat.{u} R⦄, P Q → Projective Q)
    [P.IsStableUnderRetracts]
    (hsurj : ∀ ⦃Q₁ Q₂ : ModuleCat.{u} R⦄ (f : Q₁ ⟶ Q₂),
      P Q₁ → P Q₂ →
        Function.Surjective
          (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f).hom) →
        Function.Surjective f.hom)
    (E : CochainComplex.Minus.TermsIn
      (P.map (ModuleCat.extendScalars (Ideal.Quotient.mk I))))
    (hacyclic :
      (E : CochainComplex (ModuleCat.{u} (R ⧸ I)) ℤ).Acyclic) :
    ∃ (Q : CochainComplex.Minus.TermsIn P)
      (e :
        ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
            (Q : CochainComplex (ModuleCat.{u} R) ℤ) ≅
          (E : CochainComplex (ModuleCat.{u} (R ⧸ I)) ℤ)),
      (Q : CochainComplex (ModuleCat.{u} R) ℤ).Acyclic := sorry

end CochainComplex.Minus.TermsIn

end
