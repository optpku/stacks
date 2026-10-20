module

public import ReasLib.Algebra.Module.DescentDatum.Canonical.Cosimplicial
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct TensorProduct.Right

universe u

/- Lemma 35.3.3: the cosimplicial module associated to the canonical descent
datum on `M ⊗[R] A` is canonically isomorphic to `(A/R)• ⊗[R] M`. -/
@[stacks 023I] #check (@Module.DescentDatum.canonicalCosimplicialIso :
  (R A : Type u) → [CommRing R] → [CommRing A] → [Algebra R A] →
    (M : ModuleCat.{u} R) →
      (Module.DescentDatum.canonical R A M).cosimplicial ≅
        Algebra.Amitsur.coefficients R A M)
