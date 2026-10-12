/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Localization.FiniteFamily
import StacksCheckRecall

/-!
# Lemma 15.65.14

@stack 066D

The reusable finite-family criteria are owned by `ReasLib`; this file fixes the two source clauses
and their universes with full-type checks.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u v w

/- Lemma 15.65.14 (1): `m`-pseudo-coherence descends from a finite family of principal opens whose
defining elements generate the unit ideal. -/
@[stacks 066D "Lemma 15.65.14 (1)"]
#check fun {R : Type u} [CommRing R] {ι : Type w} [Finite ι]
    (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤)
    (K : DerivedCategory (ModuleCat.{v, u} R)) (m : ℤ)
    (hloc : ∀ i, (K ⊗[R]^L[Localization.Away (f i)]).IsMPseudoCoherent m) ↦
  (DerivedCategory.IsMPseudoCoherent.of_localizationAway_unitIdeal f hunit hloc :
    K.IsMPseudoCoherent m)

/- Lemma 15.65.14 (2): pseudo-coherence descends from the same finite principal-open cover. -/
@[stacks 066D "Lemma 15.65.14 (2)"]
#check fun {R : Type u} [CommRing R] {ι : Type w} [Finite ι]
    (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤)
    (K : DerivedCategory (ModuleCat.{v, u} R))
    (hloc : ∀ i, (K ⊗[R]^L[Localization.Away (f i)]).IsPseudoCoherent) ↦
  (DerivedCategory.IsPseudoCoherent.of_localizationAway_unitIdeal f hunit hloc :
    K.IsPseudoCoherent)

#check @DerivedCategory.IsMPseudoCoherent.iff_localizationAway_unitIdeal
#check @DerivedCategory.IsPseudoCoherent.iff_localizationAway_unitIdeal
#check @DerivedCategory.IsMPseudoCoherent.of_localizationSpan
#check @DerivedCategory.IsPseudoCoherent.of_localizationSpan
