module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.GeometricallyIrreducible.FiniteType
import ReasLib.AlgebraicGeometry.Scheme.OverField.LangWeil
import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme.GeometricallyIrreducible

open AlgebraicGeometry

universe u

/- Remark 72.10.6 (1)

Every finite subset of a geometrically irreducible extension of a finite field
lies in a geometrically irreducible finite-type subalgebra.
-/
@[stacks 0BA7] #check
  (AlgebraicGeometry.FieldExtension.GeometricallyIrreducible.exists_finiteType_subalgebra :
    ∀ {k K : Type u} [Field k] [Finite k] [Field K] [Algebra k K]
      [GeometricallyIrreducible (FieldExtension.specMap k K)] (s : Finset K),
      ∃ (A : Subalgebra k K),
        Algebra.FiniteType k A ∧
          GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap k A))) ∧
            (s : Set K) ⊆ A)

/- Remark 72.10.6 (2)

Lang–Weil estimates give a homomorphism from a geometrically irreducible finite-type
algebra over a finite field to a field extension of every sufficiently large degree.
-/
@[stacks 0BA7] #check
  (AlgebraicGeometry.SchemeOverField.GeometricallyIrreducible.exists_algHom_degree :
    ∀ {k A : Type u} [Field k] [Finite k] [CommRing A] [Algebra k A]
      [Algebra.FiniteType k A]
      [GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap k A)))],
      ∃ N : ℕ, ∀ n, N ≤ n →
        ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k') (f : A →ₐ[k] k'),
          FiniteDimensional k k' ∧ Module.finrank k k' = n)

/- Remark 72.10.6 (3)

A quasi-separated algebraic space over a finite field is a scheme if it becomes
a scheme after a geometrically irreducible field extension.
-/
@[stacks 0BA7] #check
  (AlgebraicGeometry.AlgebraicSpace.IsScheme.of_isScheme_baseChange_geometricallyIrreducible :
    ∀ {k K : Type u} [Field k] [Finite k] [Field K] [Algebra k K]
      [GeometricallyIrreducible (FieldExtension.specMap k K)]
      (X : AlgebraicSpace (Spec (CommRingCat.of k)))
      [AlgebraicSpace.IsAbsolutelyQuasiSeparated X],
      AlgebraicSpace.IsScheme
        (AlgebraicSpace.baseChange (FieldExtension.specMap k K) X) →
          AlgebraicSpace.IsScheme X)
