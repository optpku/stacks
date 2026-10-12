/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Algebra.IsEpi.ModuleCat
import StacksCheckRecall

/-!
# Epimorphisms and restriction of scalars

@stack 08YS
-/

@[expose] public section

open CategoryTheory

universe u v w

section

variable {R S : Type u} [CommRing R] [CommRing S]

/- Lemma 10.107.14 (Stacks `08YS`): a commutative-ring epimorphism is exactly a ring map whose
restriction-of-scalars functor on module categories is fully faithful. -/
@[stacks 08YS]
#check (RingHom.epi_iff_restrictScalars_fullyFaithful (R := R) (S := S) :
  ∀ f : R →+* S,
    Epi (CommRingCat.ofHom f) ↔
      Nonempty ((ModuleCat.restrictScalars.{w} f).FullyFaithful))

end

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Algebra-map form, retained as the canonical reusable companion. -/
#check (Algebra.IsEpi.iff_restrictScalars_fullyFaithful (R := R) (S := S) :
  Algebra.IsEpi R S ↔
    Nonempty ((ModuleCat.restrictScalars.{w} (algebraMap R S)).FullyFaithful))

end
