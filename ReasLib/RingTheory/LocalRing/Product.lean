module

public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Data.Fintype.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Products of local rings

This leaf owns the data of a commutative ring presented as a product of local
commutative rings.  The finite-indexed refinement keeps its `Fintype` witness
as data, while the corresponding public predicates only assert that such data
exists.

@stack 04GG
@stack 09EM
-/

universe u v

namespace RingProduct

/-- A commutative-ring presentation as an indexed product of commutative rings.

Unlike `IsLocalRing.ProductDecomposition`, this generic owner does not impose localness on the
factors, so it can model products of Dedekind domains as well as products of fields. -/
@[stacks 09EM "ring product decomposition"]
structure Decomposition (R : Type u) [CommRing R] where
  /-- The index type of the factors. -/
  index : Type u
  /-- The factor carrier at each index. -/
  factor : index → Type u
  /-- The commutative-ring structures on the factors. -/
  [factorCommRing : ∀ i, CommRing (factor i)]
  /-- The ring equivalence presenting `R` as the product of its factors. -/
  equiv : R ≃+* ∀ i, factor i

attribute [instance] Decomposition.factorCommRing

namespace Decomposition

/-- An explicitly finite indexed ring-product decomposition. -/
@[stacks 09EM "finite ring product decomposition"]
structure Finite (R : Type u) [CommRing R] extends Decomposition R where
  /-- The finite enumeration of the factors. -/
  [fintype : Fintype index]

attribute [instance] Finite.fintype

/-- Build a generic ring-product decomposition from a family and a ring equivalence. -/
@[stacks 09EM "ring product decomposition constructor"]
def of {R : Type u} [CommRing R] {ι : Type u} (factors : ι → Type u)
    [∀ i, CommRing (factors i)] (equiv : R ≃+* ∀ i, factors i) : Decomposition R where
  index := ι
  factor := factors
  factorCommRing := inferInstance
  equiv := equiv

namespace Finite

/-- Build a finite ring-product decomposition from a finite family and a ring equivalence. -/
@[stacks 09EM "finite ring product decomposition constructor"]
def of {R : Type u} [CommRing R] {ι : Type u} [Fintype ι]
    (factors : ι → Type u) [∀ i, CommRing (factors i)]
    (equiv : R ≃+* ∀ i, factors i) : Finite R where
  toDecomposition := Decomposition.of factors equiv
  fintype := (inferInstance : Fintype ι)

end Finite

end Decomposition

/-- A commutative ring is a finite ring product when it admits a finite decomposition. -/
@[stacks 09EM "finite ring product predicate"]
def isFiniteProduct (R : Type u) [CommRing R] : Prop :=
  Nonempty (Decomposition.Finite R)

end RingProduct

namespace AlgProduct

/-- An algebra presentation as an indexed product of algebras over the same base. -/
@[stacks 09EM "algebra product decomposition"]
structure Decomposition
    (R : Type u) (S : Type v) [CommSemiring R] [CommRing S] [Algebra R S] where
  /-- The index type of the algebra factors. -/
  index : Type v
  /-- The factor carrier at each index. -/
  factor : index → Type v
  /-- The commutative-ring structures on the factors. -/
  [factorCommRing : ∀ i, CommRing (factor i)]
  /-- The common-base algebra structures on the factors. -/
  [factorAlgebra : ∀ i, Algebra R (factor i)]
  /-- The algebra equivalence presenting `S` as the product of its factors. -/
  equiv : S ≃ₐ[R] (∀ i, factor i)

attribute [instance] Decomposition.factorCommRing Decomposition.factorAlgebra

namespace Decomposition

/-- An explicitly finite algebra-product decomposition. -/
@[stacks 09EM "finite algebra product decomposition"]
structure Finite
    (R : Type u) (S : Type v) [CommSemiring R] [CommRing S] [Algebra R S]
    extends Decomposition R S where
  /-- The finite enumeration of the algebra factors. -/
  [fintype : Fintype index]

attribute [instance] Finite.fintype

/-- Build an algebra-product decomposition from a family and an algebra equivalence. -/
@[stacks 09EM "algebra product decomposition constructor"]
def of {R : Type u} {S : Type v} [CommSemiring R] [CommRing S] [Algebra R S]
    {ι : Type v} (factors : ι → Type v) [∀ i, CommRing (factors i)]
    [∀ i, Algebra R (factors i)] (equiv : S ≃ₐ[R] (∀ i, factors i)) :
    Decomposition R S where
  index := ι
  factor := factors
  factorCommRing := inferInstance
  factorAlgebra := inferInstance
  equiv := equiv

/-- Forgetting the common-base algebra structures yields the underlying ring-product
decomposition. -/
@[stacks 09EM "underlying ring product of an algebra product"]
def toRingProduct {R : Type u} {S : Type v} [CommSemiring R] [CommRing S] [Algebra R S]
    (D : Decomposition R S) : RingProduct.Decomposition S where
  index := D.index
  factor := D.factor
  factorCommRing := D.factorCommRing
  equiv := D.equiv.toRingEquiv

namespace Finite

/-- Build a finite algebra-product decomposition from a finite family and an algebra
equivalence. -/
@[stacks 09EM "finite algebra product decomposition constructor"]
def of {R : Type u} {S : Type v} [CommSemiring R] [CommRing S] [Algebra R S]
    {ι : Type v} [Fintype ι] (factors : ι → Type v)
    [∀ i, CommRing (factors i)] [∀ i, Algebra R (factors i)]
    (equiv : S ≃ₐ[R] (∀ i, factors i)) : Finite R S where
  toDecomposition := Decomposition.of factors equiv
  fintype := (inferInstance : Fintype ι)

/-- Forgetting the algebra structures of a finite algebra product yields a finite ring product. -/
@[stacks 09EM "underlying finite ring product of an algebra product"]
def toRingProduct {R : Type u} {S : Type v} [CommSemiring R] [CommRing S] [Algebra R S]
    (D : Finite R S) : RingProduct.Decomposition.Finite S where
  toDecomposition := D.toDecomposition.toRingProduct
  fintype := D.fintype

end Finite

end Decomposition

/-- An algebra is a finite algebra product when it admits a finite decomposition over its base. -/
@[stacks 09EM "finite algebra product predicate"]
def isFiniteProduct
    (R : Type u) (S : Type v) [CommSemiring R] [CommRing S] [Algebra R S] : Prop :=
  Nonempty (Decomposition.Finite R S)

end AlgProduct

namespace IsLocalRing

/-- A presentation of a commutative ring as a product of local commutative
rings in one ambient universe. -/
@[stacks 04GG "product decomposition into local rings"]
structure ProductDecomposition (R : Type u) [CommRing R] where
  /-- The type indexing the local factors. -/
  index : Type u
  /-- The local factor at each index. -/
  factor : index → Type u
  /-- The commutative-ring structure on each factor. -/
  [factorCommRing : ∀ i, CommRing (factor i)]
  /-- The local-ring structure on each factor. -/
  [factorIsLocalRing : ∀ i, IsLocalRing (factor i)]
  /-- The ring equivalence giving the product presentation. -/
  equiv : R ≃+* ∀ i, factor i

namespace ProductDecomposition

attribute [instance] factorCommRing factorIsLocalRing

variable {R : Type u} [CommRing R]

/-- Build a local-product decomposition from an indexed family of local rings
and a ring equivalence to its product. -/
@[stacks 04GG "local product decomposition constructor"]
def of {ι : Type u} (factors : ι → Type u)
    [∀ i, CommRing (factors i)] [∀ i, IsLocalRing (factors i)]
    (equiv : R ≃+* ∀ i, factors i) : ProductDecomposition R where
  index := ι
  factor := factors
  factorCommRing := inferInstance
  factorIsLocalRing := inferInstance
  equiv := equiv

/-- A local-product decomposition whose index type is explicitly finite. -/
@[stacks 04GG "finite product decomposition into local rings"]
structure Finite (R : Type u) [CommRing R] extends ProductDecomposition R where
  /-- The finite enumeration of the local factors. -/
  [fintype : Fintype index]

namespace Finite

attribute [instance] fintype

/-- Build a finite local-product decomposition from a finite family of local
rings and a ring equivalence to its product. -/
@[stacks 04GG "finite local product decomposition constructor"]
def of {ι : Type u} (factors : ι → Type u) [Fintype ι]
    [∀ i, CommRing (factors i)] [∀ i, IsLocalRing (factors i)]
    (equiv : R ≃+* ∀ i, factors i) : Finite R where
  toProductDecomposition := IsLocalRing.ProductDecomposition.of factors equiv
  fintype := (inferInstance : Fintype ι)

end Finite

end ProductDecomposition

/-- A commutative ring is a product of local rings when it admits a local-product
decomposition. -/
@[stacks 04GG "product of local rings"]
def isProduct (R : Type u) [CommRing R] : Prop :=
  Nonempty (ProductDecomposition R)

/-- A commutative ring is a finite product of local rings when it admits a
finite local-product decomposition. -/
@[stacks 04GG "finite product of local rings"]
def isFiniteProduct (R : Type u) [CommRing R] : Prop :=
  Nonempty (ProductDecomposition.Finite R)

namespace ProductDecomposition.Finite

variable {R : Type u} [CommRing R]

/-- Forgetting the finite enumeration of a local-product decomposition yields
the corresponding product-of-local-rings property. -/
@[stacks 04GG "finite local product is a local product"]
theorem isProduct (D : Finite R) :
    isProduct R := sorry

end ProductDecomposition.Finite

/-- Every finite product of local rings is a product of local rings. -/
@[stacks 04GG "finite product of local rings is a product of local rings"]
theorem isProduct_of_isFiniteProduct
    {R : Type u} [CommRing R] (hR : isFiniteProduct R) :
    isProduct R := sorry

end IsLocalRing
