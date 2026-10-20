/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.RingHomProperties
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Essentially Finitely Presented Algebras

This module owns the algebra and ring-homomorphism predicates for essential
finite presentation, together with their direct finite-presentation and
localization interfaces.
-/

@[expose] public section

universe u v w uP

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- An `R`-algebra `S` is essentially of finite presentation when it is the localization of a
finitely presented quotient of a finite-variable polynomial `R`-algebra. -/
@[stacks 00QM]
class EssFinitePresentation : Prop where
  cond :
    ∃ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) R)) (_ : I.FG)
      (_ : Algebra (MvPolynomial (Fin n) R ⧸ I) S)
      (_ : IsScalarTower R (MvPolynomial (Fin n) R ⧸ I) S)
      (M : Submonoid (MvPolynomial (Fin n) R ⧸ I)),
      IsLocalization M S

/-- Unfold `Algebra.EssFinitePresentation` into its finite polynomial quotient model. -/
theorem essFinitePresentation_iff :
    EssFinitePresentation R S ↔
      ∃ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) R)) (_ : I.FG)
        (_ : Algebra (MvPolynomial (Fin n) R ⧸ I) S)
        (_ : IsScalarTower R (MvPolynomial (Fin n) R ⧸ I) S)
        (M : Submonoid (MvPolynomial (Fin n) R ⧸ I)),
        IsLocalization M S := sorry

/-- A finitely presented `R`-algebra is essentially of finite presentation over `R`. -/
theorem EssFinitePresentation.of_finitePresentation [Algebra.FinitePresentation R S] :
    EssFinitePresentation R S := sorry

/-- Finite presentation canonically gives essential finite presentation. -/
instance of_finitePresentation [Algebra.FinitePresentation R S] :
    EssFinitePresentation R S := sorry

/-- A localization of a finitely presented `R`-algebra is essentially of finite presentation. -/
theorem EssFinitePresentation.of_isLocalization
    (P : Type uP) [CommRing P] [Algebra R P] [Algebra P S] [IsScalarTower R P S]
    [Algebra.FinitePresentation R P] (M : Submonoid P) [IsLocalization M S] :
    EssFinitePresentation R S := sorry

/-- Characterize essential finite presentation by an arbitrary finitely presented localization
model, allowing the model to live in the maximum ambient universe. -/
theorem essFinitePresentation_iff_exists_finitePresentation :
    EssFinitePresentation R S ↔
      ∃ (P : Type (max u v)) (_ : CommRing P) (_ : Algebra R P) (_ : Algebra P S)
        (_ : IsScalarTower R P S) (_ : Algebra.FinitePresentation R P) (M : Submonoid P),
        IsLocalization M S := sorry

/-- The identity `R`-algebra is essentially of finite presentation over `R`. -/
instance instEssFinitePresentationSelf : EssFinitePresentation R R := sorry

/-- Essential finite presentation is invariant under equivalence of `R`-algebras. -/
theorem EssFinitePresentation.equiv (T : Type w) [CommRing T] [Algebra R T]
    [EssFinitePresentation R S] (e : S ≃ₐ[R] T) : EssFinitePresentation R T := sorry

/-- An essentially finitely presented algebra is essentially of finite type. -/
theorem EssFinitePresentation.toEssFiniteType (h : EssFinitePresentation R S) :
    EssFiniteType R S := sorry

/-- Essential finite presentation canonically gives essential finite type. -/
instance instEssFiniteTypeOfEssFinitePresentation [EssFinitePresentation R S] :
    EssFiniteType R S := sorry

end Algebra

namespace RingHom

/-- A ring homomorphism whose target is a localization of a quotient of its source. -/
def IsLocalizationOfQuotient (f : R →+* S) : Prop :=
  ∃ (I : Ideal R) (_ : Algebra (R ⧸ I) S) (M : Submonoid (R ⧸ I))
    (_ : IsLocalization M S),
      f = (algebraMap (R ⧸ I) S).comp (Ideal.Quotient.mk I)

/-- A surjective ring homomorphism is a localization of its kernel quotient.
This is the canonical quotient presentation of a surjection, with the
localization submonoid chosen to be the units of the quotient. -/
@[stacks 00QM "surjective localization of quotient"]
theorem isLocalizationOfQuotient_of_surjective (f : R →+* S)
    (hf : Function.Surjective f) : f.IsLocalizationOfQuotient := sorry

/-- A ring map is essentially of finite presentation when its induced source algebra has that
property. -/
@[stacks 00QM, algebraize Algebra.EssFinitePresentation]
def EssFinitePresentation (f : R →+* S) : Prop :=
  -- Local instance justification (noncanonical choice): The explicit ring map f selects the R-algebra structure on S used by this predicate.
  letI := f.toAlgebra
  Algebra.EssFinitePresentation R S

/-- Characterize an essentially finitely presented ring map using an algebra localization model. -/
theorem essFinitePresentation_iff (f : R →+* S) :
    f.EssFinitePresentation ↔
      -- Local instance justification (noncanonical choice): The localization model and its scalar tower must use the R-algebra structure on S induced by f.
      letI := f.toAlgebra
      ∃ (P : Type (max u v)) (_ : CommRing P) (_ : Algebra R P) (_ : Algebra P S)
        (_ : IsScalarTower R P S) (_ : Algebra.FinitePresentation R P) (M : Submonoid P),
        IsLocalization M S := sorry

/-- Characterize an essentially finitely presented ring map as a finitely presented map followed
by a localization. -/
theorem essFinitePresentation_iff_exists_finitePresentation (f : R →+* S) :
    f.EssFinitePresentation ↔
      ∃ (P : Type (max u v)) (_ : CommRing P) (g : R →+* P) (_ : g.FinitePresentation)
        (M : Submonoid P) (_ : Algebra P S) (_ : IsLocalization M S),
        f = (algebraMap P S).comp g := sorry

/-- Relate the ring-homomorphism and algebra forms of essential finite presentation. -/
@[simp]
theorem essFinitePresentation_algebraMap [Algebra R S] :
    (algebraMap R S).EssFinitePresentation ↔ Algebra.EssFinitePresentation R S := sorry

namespace EssFinitePresentation

/-- The identity ring map is essentially of finite presentation. -/
theorem id (R : Type u) [CommRing R] : (RingHom.id R).EssFinitePresentation := sorry

end EssFinitePresentation

end RingHom
