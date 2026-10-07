module

public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.FinitePartDecomposition
public import ReasLib.RingTheory.Ideal.Over
public import ReasLib.RingTheory.LocalRing.Product

@[expose] public section

/-!
# Quasi-finite product decompositions over a selected prime

@stack 00UK
@stack 00UL

This leaf owns the decomposition independently of how the base ring was
obtained.  In particular, etale extensions, henselian rings, and local
arguments can share the same finite-factor and residual-factor API.
-/

universe u v

namespace PrimeSpectrum

/-- A finite-part decomposition of an algebra in which the finite part is an
explicit finite product, with one selected point above `p` in each factor and
no quasi-finite point above `p` in the remainder. -/
@[stacks 00UL "quasi-finite product decomposition"]
structure QuasiFiniteDecomposition
    {R : Type u} [CommRing R] (p : PrimeSpectrum R)
    (S : Type v) [CommRing S] [Algebra R S] where
  /-- The finite-part decomposition of the source algebra. -/
  finitePart : Algebra.FinitePartDecomposition R S
  /-- The finite part as an explicitly finite product of algebras. -/
  factors : AlgProduct.Decomposition.Finite R finitePart.finitePart
  /-- The selected prime above `p` in each finite factor. -/
  factorPoint : ∀ i, p.asIdeal.primesOver (factors.factor i)
  /-- Each finite factor has a unique prime above `p`. -/
  [factorPointUnique : ∀ i, Subsingleton (p.asIdeal.primesOver (factors.factor i))]
  /-- The residual factor has no quasi-finite point above `p`. -/
  remainderNotQuasiFinite :
    ∀ q : p.asIdeal.primesOver finitePart.remainder,
      ¬ Algebra.QuasiFiniteAt R q.1

namespace QuasiFiniteDecomposition

attribute [instance] factorPointUnique

/-- Build a quasi-finite product decomposition from a finite-part
decomposition, a finite product presentation of its finite part, and the
selected fiber data. -/
@[stacks 00UL "quasi-finite product decomposition constructor"]
def of {R : Type u} [CommRing R] (p : PrimeSpectrum R)
    {S : Type v} [CommRing S] [Algebra R S]
    (finitePart : Algebra.FinitePartDecomposition R S)
    (factors : AlgProduct.Decomposition.Finite R finitePart.finitePart)
    (factorPoint : ∀ i, p.asIdeal.primesOver (factors.factor i))
    [factorPointUnique : ∀ i, Subsingleton (p.asIdeal.primesOver (factors.factor i))]
    (remainderNotQuasiFinite :
      ∀ q : p.asIdeal.primesOver finitePart.remainder,
        ¬ Algebra.QuasiFiniteAt R q.1) : QuasiFiniteDecomposition p S where
  finitePart := finitePart
  factors := factors
  factorPoint := factorPoint
  factorPointUnique := factorPointUnique
  remainderNotQuasiFinite := remainderNotQuasiFinite

/-- The finite index type of the product factors. -/
@[stacks 00UL "index of a quasi-finite product decomposition"]
abbrev ι {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S]
    (D : QuasiFiniteDecomposition p S) := D.factors.index

/-- A finite factor of a quasi-finite product decomposition. -/
@[stacks 00UL "factor of a quasi-finite product decomposition"]
abbrev factor {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S]
    (D : QuasiFiniteDecomposition p S) (i : D.ι) := D.factors.factor i

/-- The residual factor of a quasi-finite product decomposition. -/
@[stacks 00UL "remainder of a quasi-finite product decomposition"]
abbrev remainder {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S]
    (D : QuasiFiniteDecomposition p S) := D.finitePart.remainder

/-- Each product factor is module-finite over the base ring. -/
@[stacks 00UL "finite factor of a quasi-finite product decomposition"]
instance factorFinite {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S]
    (D : QuasiFiniteDecomposition p S) (i : D.ι) :
    Module.Finite R (D.factor i) :=
  Module.Finite.of_surjective
    ((LinearMap.proj (R := R) i).comp D.factors.equiv.toLinearMap)
    ((LinearMap.proj_surjective (R := R) i).comp D.factors.equiv.surjective)

/-- The algebra equivalence exhibiting the complete product decomposition. -/
@[stacks 00UL "algebra equivalence of a quasi-finite product decomposition"]
noncomputable def equiv {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S]
    (D : QuasiFiniteDecomposition p S) :
    S ≃ₐ[R] ((i : D.ι) → D.factor i) × D.remainder :=
  D.finitePart.equiv.trans
    (AlgEquiv.prodCongr D.factors.equiv
      (AlgEquiv.refl : D.remainder ≃ₐ[R] D.remainder))

/-- The finiteness, selected-point uniqueness, and residual-factor conditions
carried by a quasi-finite product decomposition.  The product equivalence is
available separately as `D.equiv`. -/
@[stacks 00UL "quasi-finite product decomposition specification"]
theorem spec {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S]
    (D : QuasiFiniteDecomposition p S) :
    (∀ i, Module.Finite R (D.factor i)) ∧
      (∀ i, Nonempty (p.asIdeal.primesOver (D.factor i))) ∧
      (∀ i, Subsingleton (p.asIdeal.primesOver (D.factor i))) ∧
      (∀ q : p.asIdeal.primesOver D.remainder,
        ¬ Algebra.QuasiFiniteAt R q.1) :=
  ⟨fun i ↦ D.factorFinite i, fun i ↦ ⟨D.factorPoint i⟩,
    fun i ↦ inferInstance, D.remainderNotQuasiFinite⟩

/-- The canonical residue-field map at a selected finite factor. -/
@[stacks 00UL "residue field map of a quasi-finite factor"]
noncomputable def factorResidueMap
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S]
    (D : QuasiFiniteDecomposition p S) (i : D.ι) :
    p.asIdeal.ResidueField →+* (D.factorPoint i).1.ResidueField :=
  Ideal.ResidueField.map p.asIdeal (D.factorPoint i).1
    (algebraMap R (D.factor i)) (D.factorPoint i).2.2.over

/-- The non-global algebra structure induced by a selected factor's canonical
residue-field map. -/
@[stacks 00UL "residue field algebra of a quasi-finite factor", implicit_reducible]
noncomputable def factorResidueAlgebra
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S]
    (D : QuasiFiniteDecomposition p S) (i : D.ι) :
    Algebra p.asIdeal.ResidueField (D.factorPoint i).1.ResidueField :=
  (D.factorResidueMap i).toAlgebra

/-- The canonical residue-field map at each finite factor is finite. -/
@[stacks 00UL "finite residue field map of a quasi-finite factor"]
theorem factorResidueMap_finite
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S]
    (D : QuasiFiniteDecomposition p S) (i : D.ι) :
    (D.factorResidueMap i).Finite := sorry

/-- The fiber of a finite factor is exactly its selected point. -/
@[stacks 00UL "singleton fiber of a quasi-finite factor"]
theorem factorPrimesOver_eq_singleton
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S]
    (D : QuasiFiniteDecomposition p S) (i : D.ι) :
    p.asIdeal.primesOver (D.factor i) =
      ({(D.factorPoint i).1} : Set (Ideal (D.factor i))) := sorry

end QuasiFiniteDecomposition

end PrimeSpectrum
