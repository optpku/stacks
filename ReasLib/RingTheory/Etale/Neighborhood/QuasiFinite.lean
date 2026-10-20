/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Etale.Neighborhood
public import ReasLib.RingTheory.Ideal.Over
public import ReasLib.RingTheory.QuasiFinite.Decomposition

@[expose] public section

/-!
# Quasi-finite decompositions over etale neighborhoods

@stack 00UK

This leaf packages the finite-product output that occurs after passing to an
etale neighborhood of a prime. The finite part and the residual
quasi-finite-free factor are data; residue-field refinements are separate
predicates on that data.
-/

universe u v w

namespace PrimeSpectrum.EtaleNeighborhood

open scoped TensorProduct

/-- A finite-product decomposition after an etale neighborhood of a prime.

The selected point of `neighborhood` controls all fiber conditions. Keeping it
bundled prevents consumers from rebuilding the same etale neighborhood and
residue-field identification with incompatible definitional equalities. -/
@[stacks 00UK "quasi-finite finite-product decomposition"]
structure QuasiFiniteDecomposition
    {R : Type u} [CommRing R] (p : PrimeSpectrum R)
    {S : Type v} [CommRing S] [Algebra R S] where
  /-- The etale neighborhood over the selected base point. -/
  neighborhood : EtaleNeighborhood.{u, w} p
  /-- The reusable product decomposition over the neighborhood's selected
  point. -/
  product : PrimeSpectrum.QuasiFiniteDecomposition neighborhood.point
    (neighborhood.carrier ⊗[R] S)

namespace QuasiFiniteDecomposition

/-- The finite index type supplied by the underlying product decomposition. -/
abbrev ι
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S]
    (D : QuasiFiniteDecomposition.{u, v, w} p (S := S)) := D.product.ι

/-- A finite factor of the underlying product decomposition. -/
abbrev factor
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S]
    (D : QuasiFiniteDecomposition.{u, v, w} p (S := S)) (i : D.ι) :=
  D.product.factor i

/-- The residual factor of the underlying product decomposition. -/
abbrev remainder
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S]
    (D : QuasiFiniteDecomposition.{u, v, w} p (S := S)) :=
  D.product.remainder

/-- The selected point in a finite factor. -/
abbrev factorPoint
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S]
    (D : QuasiFiniteDecomposition.{u, v, w} p (S := S)) (i : D.ι) :=
  D.product.factorPoint i

/-- The algebra equivalence supplied by the underlying product
decomposition. -/
noncomputable def decomposition
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S]
    (D : QuasiFiniteDecomposition.{u, v, w} p (S := S)) :
    D.neighborhood.carrier ⊗[R] S ≃ₐ[D.neighborhood.carrier]
      ((i : D.ι) → D.factor i) × D.remainder :=
  D.product.equiv

/-- The residual factor has no quasi-finite point over the selected
neighborhood point. -/
theorem remainderNotQuasiFinite
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S]
    (D : QuasiFiniteDecomposition.{u, v, w} p (S := S)) :
    ∀ q : D.neighborhood.point.asIdeal.primesOver D.remainder,
      ¬ Algebra.QuasiFiniteAt D.neighborhood.carrier q.1 :=
  D.product.remainderNotQuasiFinite

/-- Build the neighborhood-level package from an explicit etale neighborhood
and a product decomposition over its selected point. -/
@[stacks 00UK "etale-neighborhood quasi-finite decomposition constructor"]
noncomputable def of
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S]
    (N : EtaleNeighborhood.{u, w} p)
    (D : PrimeSpectrum.QuasiFiniteDecomposition N.point (N.carrier ⊗[R] S)) :
    QuasiFiniteDecomposition.{u, v, w} p (S := S) where
  neighborhood := N
  product := D

/-- The etale, fiber, finiteness, and non-quasi-finite-remainder properties
carried by a quasi-finite decomposition.  The product equivalence itself is
available directly as `D.decomposition`. -/
@[stacks 00UK "quasi-finite decomposition specification"]
theorem spec
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S]
    (D : QuasiFiniteDecomposition.{u, v, w} p (S := S)) :
    Algebra.Etale R D.neighborhood.carrier ∧
      p.asIdeal =
        Ideal.comap (algebraMap R D.neighborhood.carrier) D.neighborhood.point.asIdeal ∧
      Function.Bijective
        (Ideal.ResidueField.map p.asIdeal D.neighborhood.point.asIdeal
          (algebraMap R D.neighborhood.carrier) D.neighborhood.over) ∧
      (∀ i, Module.Finite D.neighborhood.carrier (D.factor i)) ∧
      (∀ i, Nonempty (D.neighborhood.point.asIdeal.primesOver (D.factor i))) ∧
      (∀ i, Subsingleton (D.neighborhood.point.asIdeal.primesOver (D.factor i))) ∧
      (∀ q : D.neighborhood.point.asIdeal.primesOver D.remainder,
        ¬ Algebra.QuasiFiniteAt D.neighborhood.carrier q.1) := by
  rcases D.product.spec with ⟨hfinite, hpoint, hunique, hremainder⟩
  exact ⟨inferInstance, D.neighborhood.over,
    D.neighborhood.residueField_bijective, hfinite, hpoint, hunique,
    hremainder⟩

/-- The canonical residue-field map at a selected finite factor. -/
@[stacks 00UK "residue field map of a quasi-finite factor"]
noncomputable def factorResidueMap
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S]
    (D : QuasiFiniteDecomposition.{u, v, w} p (S := S)) (i : D.ι) :
    D.neighborhood.point.asIdeal.ResidueField →+*
      (D.factorPoint i).1.ResidueField :=
  D.product.factorResidueMap i

/-- The explicit algebra structure on the residue field of a selected factor,
induced by `factorResidueMap`.  It remains an explicit value because the
selected decomposition is not global ambient structure. -/
@[stacks 00UK "residue field algebra of a quasi-finite factor", implicit_reducible]
noncomputable def factorResidueAlgebra
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S]
    (D : QuasiFiniteDecomposition.{u, v, w} p (S := S)) (i : D.ι) :
    Algebra D.neighborhood.point.asIdeal.ResidueField (D.factorPoint i).1.ResidueField :=
  D.product.factorResidueAlgebra i

/-- The canonical residue-field map at a selected finite factor is finite. -/
@[stacks 00UK "finite residue field map of a quasi-finite factor"]
theorem factorResidueMap_finite
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S]
    (D : QuasiFiniteDecomposition.{u, v, w} p (S := S)) (i : D.ι) :
    (D.factorResidueMap i).Finite :=
  D.product.factorResidueMap_finite i

/-- The fiber of a finite factor is exactly its selected point. -/
@[stacks 00UK "singleton fiber of a quasi-finite factor"]
theorem factorPrimesOver_eq_singleton
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S]
    (D : QuasiFiniteDecomposition.{u, v, w} p (S := S)) (i : D.ι) :
    D.neighborhood.point.asIdeal.primesOver (D.factor i) =
      ({(D.factorPoint i).1} : Set (Ideal (D.factor i))) :=
  D.product.factorPrimesOver_eq_singleton i

/-- Lemma 10.145.3: a finite-type algebra admits a quasi-finite product decomposition
after an etale neighborhood of any selected prime. -/
@[stacks 00UK]
theorem nonempty
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (p : PrimeSpectrum R) :
    Nonempty (QuasiFiniteDecomposition.{u, v, u} p (S := S)) := sorry

end QuasiFiniteDecomposition

end PrimeSpectrum.EtaleNeighborhood
