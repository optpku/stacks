module

public import ReasLib.RingTheory.CotangentComplex.TensorProduct
public import ReasLib.Algebra.Category.ModuleCat.Tor.Independence

/-!
# Tor-independent tensor products and cotangent complexes

For Tor-independent commutative algebras over a common base, the canonical
cotangent comparison for the tensor product is an isomorphism and its cone
vanishes.  The resulting cotangent object is represented by the biproduct of
the two scalar-extended cotangent complexes.
-/

@[expose] public section

open Algebra.CotangentComplex
open CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Algebra.CotangentComplex

/-- The canonical tensor-product cotangent cone vanishes for Tor-independent
commutative algebras. -/
@[stacks 09DA]
theorem tensorProductCone_isZero_of_torIndependent (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (h_torIndependent :
      ModuleCat.Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R B)) :
    IsZero (tensorProductCone R A B) :=
  sorry

/-- The canonical sum map from the two scalar-extended cotangent complexes to
the cotangent complex of a tensor product is an isomorphism under Tor
independence. -/
@[stacks 09DA]
theorem sumMap_isIso_of_torIndependent (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (h_torIndependent :
      ModuleCat.Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R B)) :
    IsIso (sumMap R A B) :=
  sorry

/-- The cotangent complex of a Tor-independent tensor product is represented in
the derived category by the biproduct of the two scalar-extended cotangent
complexes. -/
theorem isIsomorphic_derived_sumMapSource_of_torIndependent (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (h_torIndependent :
      ModuleCat.Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R B)) :
    IsIsomorphic (derived R (A ⊗[R] B))
      (DerivedCategory.Q.obj
        (tensorProductExtendLeft R A B ⊞ tensorProductExtendRight R A B)) :=
  sorry

/-- The canonical tensor-product sum map is an isomorphism whenever its
Tor-independence hypothesis is available through `Fact`. -/
instance sumMap_isIso_of_fact_torIndependent (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    [Fact (ModuleCat.Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R B))] :
    IsIso (sumMap R A B) :=
  sumMap_isIso_of_torIndependent R A B Fact.out

end Algebra.CotangentComplex
