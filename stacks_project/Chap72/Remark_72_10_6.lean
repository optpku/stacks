module

public import Mathlib.Data.Finite.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.GeometricallyIrreducible
public import stacks_project.Chap65.Lemma_65_16_1_ChangeOfBase
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme

/-!
# Geometrically irreducible extensions over finite fields

Over a finite field, a geometrically irreducible extension is a directed colimit
of geometrically irreducible finite-type algebras, which admit degree-`n` points
for all sufficiently large `n`. Quasi-separated algebraic spaces that become
schemes after such a base change are themselves schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat

noncomputable section

universe u

namespace AlgebraicGeometry.FieldExtension.GeometricallyIrreducible

/-- Remark 72.10.6 (1): Let `k` be a finite field and let `K/k` be a geometrically
irreducible field extension. Then `K` is a directed colimit of geometrically
irreducible finite-type `k`-algebras: every finite set of elements of `K` is
contained in a finite-type `k`-subalgebra `A` for which
`Spec.map (CommRingCat.ofHom (algebraMap k A))` is geometrically irreducible. -/
@[stacks 0BA7]
theorem exists_finiteType_subalgebra {k K : Type u} [Field k] [Finite k] [Field K]
    [Algebra k K] [GeometricallyIrreducible (FieldExtension.specMap k K)]
    (s : Finset K) :
    ∃ (A : Subalgebra k K),
      Algebra.FiniteType k A ∧
        GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap k A))) ∧
          (s : Set K) ⊆ A :=
  sorry

/-- Every finite-type `k`-subalgebra of a geometrically irreducible field extension
`K/k` is geometrically irreducible over `k`. -/
theorem finiteType_subalgebra {k K : Type u} [Field k] [Field K] [Algebra k K]
    [GeometricallyIrreducible (FieldExtension.specMap k K)] (A : Subalgebra k K)
    [Algebra.FiniteType k A] :
    GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap k A))) :=
  sorry

end AlgebraicGeometry.FieldExtension.GeometricallyIrreducible

namespace AlgebraicGeometry.SchemeOverField.GeometricallyIrreducible

/-- Remark 72.10.6 (2): Let `k` be a finite field and let `A` be a geometrically
irreducible finite-type `k`-algebra. Then for all sufficiently large `n` there
exists a field extension `k'/k` of degree `n` together with a `k`-algebra
homomorphism `A →ₐ[k] k'`. -/
@[stacks 0BA7]
theorem exists_algHom_degree {k A : Type u} [Field k] [Finite k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A]
    [GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap k A)))] :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k'),
        FiniteDimensional k k' ∧ Module.finrank k k' = n ∧
          Nonempty (A →ₐ[k] k') :=
  sorry

end AlgebraicGeometry.SchemeOverField.GeometricallyIrreducible

namespace AlgebraicGeometry.AlgebraicSpace.IsScheme

/-- Remark 72.10.6 (3): Let `k` be a finite field and let `K/k` be a geometrically
irreducible field extension. If `X` is a quasi-separated algebraic space over `k`
whose base change along `FieldExtension.specMap k K` is a scheme, then `X` is a
scheme. -/
@[stacks 0BA7]
theorem of_isScheme_baseChange_geometricallyIrreducible {k K : Type u} [Field k]
    [Finite k] [Field K] [Algebra k K]
    [GeometricallyIrreducible (FieldExtension.specMap k K)]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) [IsAbsolutelyQuasiSeparated X]
    (hX : IsScheme (baseChange (FieldExtension.specMap k K) X)) :
    IsScheme X :=
  sorry

/-- If a quasi-separated algebraic space over a finite field becomes a scheme after
base change along some geometrically irreducible field extension, then it is a
scheme. -/
theorem of_baseChange_geometricallyIrreducible {k : Type u} [Field k] [Finite k]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) [IsAbsolutelyQuasiSeparated X]
    (hX :
      ∃ (K : Type u) (_ : Field K) (_ : Algebra k K)
        (_ : GeometricallyIrreducible (FieldExtension.specMap k K)),
        IsScheme (baseChange (FieldExtension.specMap k K) X)) :
    IsScheme X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsScheme
