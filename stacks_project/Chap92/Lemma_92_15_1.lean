module

public import ReasLib.RingTheory.CotangentComplex.TensorProduct.TorIndependent
import StacksCheckRecall

open Algebra.CotangentComplex
open CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct

universe u

/- Lemma 92.15.1. The scalar-extended standard cotangent complexes represent
   the two derived extensions, and tensor associativity identifies them with
   `L_{A/R} ⊗[R] B` and `L_{B/R} ⊗[R] A`. -/
@[stacks 09DA] #check (Algebra.CotangentComplex.tensorProductCone_isZero_of_torIndependent :
  ∀ (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B],
    ModuleCat.Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R B) →
    IsZero (Algebra.CotangentComplex.tensorProductCone R A B))

#check (Algebra.CotangentComplex.sumMap_isIso_of_torIndependent :
  ∀ (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B],
    ModuleCat.Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R B) →
    IsIso (Algebra.CotangentComplex.sumMap R A B))

#check (Algebra.CotangentComplex.isIsomorphic_derived_sumMapSource_of_torIndependent :
  ∀ (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B],
    ModuleCat.Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R B) →
    IsIsomorphic (Algebra.CotangentComplex.derived R (A ⊗[R] B))
      (DerivedCategory.Q.obj
        (Algebra.CotangentComplex.tensorProductExtendLeft R A B ⊞
          Algebra.CotangentComplex.tensorProductExtendRight R A B)))
