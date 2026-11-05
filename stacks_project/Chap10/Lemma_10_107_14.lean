/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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

variable {R S : Type u} [CommRing R] [CommRing S] [Small.{w} S]

/- Lemma 10.107.14 (Stacks `08YS`): when `S` is small in the module universe, a commutative-ring
epimorphism is exactly a ring map whose restriction-of-scalars functor is fully faithful. -/
@[stacks 08YS]
#check (RingHom.epi_iff_restrictScalars_fullyFaithful (R := R) (S := S) :
  ∀ f : R →+* S,
    Epi (CommRingCat.ofHom f) ↔
      Nonempty ((ModuleCat.restrictScalars.{w} f).FullyFaithful))

end

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Small.{w} S]

/- Algebra-map form, with the same size condition on `S`. -/
#check (Algebra.IsEpi.iff_restrictScalars_fullyFaithful (R := R) (S := S) :
  Algebra.IsEpi R S ↔
    Nonempty ((ModuleCat.restrictScalars.{w} (algebraMap R S)).FullyFaithful))

end
