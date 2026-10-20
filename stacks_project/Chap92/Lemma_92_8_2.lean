module

public import ReasLib.RingTheory.CotangentComplex.Localization
import StacksCheckRecall

/-!
# Vanishing of the cotangent complex along a derived diagonal

If `A → B` is a ring map with `B = B ⊗[A]^L B` in `D(B)`, then `L_{B/A}`
vanishes in `D(B)`.
-/

@[expose] public section

universe u

/- Lemma 92.8.2. Let `A → B` be a ring map such that `B = B ⊗[A]^L B`.
Then `L_{B/A} = 0` in `D(B)`, as vanishing of `derived A B`. -/
@[stacks 08R0] #check (Algebra.CotangentComplex.isZero_derived_of_derivedTensor :
  ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B],
    RingedSite.Cotangent.Functoriality.InducesDerivedTensorQuasiIso
      (Algebra.CotangentComplex.idCodomainCommSq A B B) →
    CategoryTheory.Limits.IsZero (Algebra.CotangentComplex.derived A B))

/- Under the derived-tensor identity `B = B ⊗[A]^L B`, every homology module of
`Algebra.cotangentComplex A B` vanishes. -/
#check (Algebra.CotangentComplex.isZero_homology_of_derivedTensor :
  ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B],
    RingedSite.Cotangent.Functoriality.InducesDerivedTensorQuasiIso
      (Algebra.CotangentComplex.idCodomainCommSq A B B) →
    ∀ {n : ℤ}, CategoryTheory.Limits.IsZero ((Algebra.cotangentComplex A B).homology n))
