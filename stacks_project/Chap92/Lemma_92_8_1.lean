module

public import ReasLib.RingTheory.CotangentComplex.Localization
import StacksCheckRecall

/-!
# Localization of the cotangent complex at the bottom

If `A → A' → B` are ring maps with `B = B ⊗[A]^L A'` in `D(A')`, then the
canonical comparison `toRelativeMap : L_{B/A} ⟶ L_{B/A'}` is an isomorphism
in `D(B)`.
-/

@[expose] public section

universe u

/- Lemma 92.8.1. Let `A → A' → B` be ring maps such that `B = B ⊗[A]^L A'`.
Then `L_{B/A} = L_{B/A'}` in `D(B)`, via the canonical comparison. -/
@[stacks 08QZ] #check (Algebra.CotangentComplex.toRelativeMap_isIso_of_derivedTensor :
  ∀ (A A' B : Type u) [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A' B] [Algebra A B] [IsScalarTower A A' B],
    RingedSite.Cotangent.Functoriality.InducesDerivedTensorQuasiIso
      (Algebra.CotangentComplex.idCodomainCommSq A A' B) →
    CategoryTheory.IsIso (Algebra.CotangentComplex.toRelativeMap A A' B))
