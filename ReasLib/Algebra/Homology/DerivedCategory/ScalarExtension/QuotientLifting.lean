/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.RingTheory.Henselian
public import ReasLib.Algebra.Category.ModuleCat.FiniteProjective
public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Termwise.Minus
public import ReasLib.Algebra.Homology.DerivedCategory.ProjectiveModel
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.Algebra.Module.StableFree
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lifting bounded-above derived models across quotient maps

This leaf records the general term-class lifting theorem and its projective, finite-stably-free,
and henselian finite-projective specializations.

@stack 0BCA
@stack 09AR
@stack 0BCB
@stack 0BCE
-/

@[expose] public section

noncomputable section

open CategoryTheory
open ComplexShape
open scoped DerivedTensorWithAlgebra

universe u

-- Local instance justification (instance diamond): the source statements use the standard
-- derived category and its canonical quotient functor on explicit cochain representatives.
attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.DerivedCategory.QuotientLifting

variable {R : Type u} [CommRing R]

/-- Lemma 15.76.2: a bounded-above representative with terms in a projective object property
lifts from `R ⧸ I` to `R` when surjectivity lifts inside that property. -/
@[stacks 0BCA "bounded-above term-class lifting"]
theorem exists_termsIn
    (I : Ideal R) (PClass : ObjectProperty (ModuleCat R))
    (hprojective : ∀ ⦃P : ModuleCat R⦄, PClass P → Projective P)
    [PClass.IsClosedUnderBinaryCoproducts]
    [PClass.IsStableUnderRetracts]
    (hsurj : ∀ ⦃P₁ P₂ : ModuleCat R⦄ (f : P₁ ⟶ P₂),
      PClass P₁ → PClass P₂ →
        Function.Surjective
            ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f).hom →
          Function.Surjective f.hom)
    (K : DerivedCategory (ModuleCat R))
    (E : CochainComplex.Minus.TermsIn
      (PClass.map (ModuleCat.extendScalars (Ideal.Quotient.mk I))))
    (hErep : Nonempty
      ((K ⊗[R]^L[(R ⧸ I)]) ≅
        DerivedCategory.Q.obj (E : CochainComplex (ModuleCat (R ⧸ I)) ℤ)))
    (hKrep : ∃ P : CochainComplex.Minus.TermsIn PClass,
      IsIsomorphic K
        (DerivedCategory.Q.obj (P : CochainComplex (ModuleCat R) ℤ))) :
    ∃ P : CochainComplex.Minus.TermsIn PClass,
      IsIsomorphic K
          (DerivedCategory.Q.obj (P : CochainComplex (ModuleCat R) ℤ)) ∧
        IsIsomorphic
          (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (P : CochainComplex (ModuleCat R) ℤ))
          (E : CochainComplex (ModuleCat (R ⧸ I)) ℤ) := sorry

/-- Lemma 15.76.3: a bounded-above projective model lifts across a nilpotent quotient. -/
@[stacks 09AR "bounded-above projective lifting across a nilpotent quotient"]
theorem exists_projective
    (I : Ideal R) (K : DerivedCategory (ModuleCat R))
    (E : CochainComplex.ProjectiveMinus (ModuleCat (R ⧸ I)))
    (hErep : IsIsomorphic (K ⊗[R]^L[(R ⧸ I)])
      (DerivedCategory.Q.obj (E : CochainComplex (ModuleCat (R ⧸ I)) ℤ)))
    (hInil : IsNilpotent I) :
    ∃ P : CochainComplex.ProjectiveMinus (ModuleCat R),
      IsIsomorphic K
          (DerivedCategory.Q.obj (P : CochainComplex (ModuleCat R) ℤ)) ∧
        IsIsomorphic
          (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (P : CochainComplex (ModuleCat R) ℤ))
          (E : CochainComplex (ModuleCat (R ⧸ I)) ℤ) := sorry

/-- Lemma 15.76.5: a bounded-above finite-stably-free model lifts across a quotient by an ideal
contained in the Jacobson radical, preserving termwise freeness. -/
@[stacks 0BCB "bounded-above finite-stably-free lifting"]
theorem exists_finiteStablyFree
    (I : Ideal R) (K : DerivedCategory (ModuleCat R))
    (E : CochainComplex.Minus.TermsIn
      (finiteStablyFreeModuleProperty (R ⧸ I)))
    (hErep : Nonempty
      ((K ⊗[R]^L[(R ⧸ I)]) ≅
        DerivedCategory.Q.obj (E : CochainComplex (ModuleCat (R ⧸ I)) ℤ)))
    (hK : K.IsPseudoCoherent) (hI : I ≤ Ring.jacobson R) :
    ∃ P : CochainComplex.Minus.TermsIn (finiteStablyFreeModuleProperty R),
      IsIsomorphic K
          (DerivedCategory.Q.obj (P : CochainComplex (ModuleCat R) ℤ)) ∧
        IsIsomorphic
          (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (P : CochainComplex (ModuleCat R) ℤ))
          (E : CochainComplex (ModuleCat (R ⧸ I)) ℤ) ∧
        ∀ i : ℤ,
          Module.Free (R ⧸ I) ((E : CochainComplex (ModuleCat (R ⧸ I)) ℤ).X i) →
            Module.Free R ((P : CochainComplex (ModuleCat R) ℤ).X i) := sorry

/-- Lemma 15.76.9: a bounded-above finite-projective model lifts across a henselian quotient,
preserving termwise freeness. -/
@[stacks 0BCE "bounded-above finite-projective lifting across a henselian quotient"]
theorem exists_finiteProjective
    (I : Ideal R) [HenselianRing R I]
    (K : DerivedCategory (ModuleCat R))
    (E : CochainComplex.Minus.TermsIn (ModuleCat.finiteProjective (R ⧸ I)))
    (hErep : Nonempty
      ((K ⊗[R]^L[(R ⧸ I)]) ≅
        DerivedCategory.Q.obj (E : CochainComplex (ModuleCat (R ⧸ I)) ℤ)))
    (hK : K.IsPseudoCoherent) :
    ∃ P : CochainComplex.Minus.TermsIn (ModuleCat.finiteProjective R),
      IsIsomorphic K
          (DerivedCategory.Q.obj (P : CochainComplex (ModuleCat R) ℤ)) ∧
        IsIsomorphic
          (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (P : CochainComplex (ModuleCat R) ℤ))
          (E : CochainComplex (ModuleCat (R ⧸ I)) ℤ) ∧
        ∀ i : ℤ,
          Module.Free (R ⧸ I) ((E : CochainComplex (ModuleCat (R ⧸ I)) ℤ).X i) →
            Module.Free R ((P : CochainComplex (ModuleCat R) ℤ).X i) := sorry

end CategoryTheory.DerivedCategory.QuotientLifting
