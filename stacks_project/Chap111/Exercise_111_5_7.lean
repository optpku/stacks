/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalRing.ResidueField.FlatExtension
import StacksCheckRecall

@[expose] public section

universe u v

/- Exercise 111.5.7: if `R` is a local ring and `K` is a finite field extension of
`ResidueField R`, there exists a flat local map of local rings `R → R'` such that
`maximalIdeal R' = Ideal.map (algebraMap R R') (maximalIdeal R)` and
`ResidueField R' ≃ₐ[ResidueField R] K`. -/
@[stacks 02CW]
#check (@IsLocalRing.ResidueField.exists_flat_localExtension_of_finiteDimensional :
  ∀ {R : Type u} [CommRing R] [IsLocalRing R]
    (K : Type v) [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    [FiniteDimensional (IsLocalRing.ResidueField R) K],
    ∃ (R' : Type (max u v)) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R')
      (_ : IsLocalHom (algebraMap R R')) (_ : (algebraMap R R').Flat)
      (_ : IsLocalRing.ResidueField R' ≃ₐ[IsLocalRing.ResidueField R] K),
      Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) =
        IsLocalRing.maximalIdeal R')
