module

public import Mathlib.Data.Finite.Defs
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.GeometricallyIrreducible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme.FieldExtension

/-!
# Scheme descent along geometrically irreducible field extensions

A quasi-separated algebraic space over a finite field is a scheme if it becomes
a scheme after a geometrically irreducible field extension.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsScheme

/-- A quasi-separated algebraic space over a finite field is a scheme if its base
change along a geometrically irreducible field extension is a scheme. -/
@[stacks 0BA7]
theorem of_isScheme_baseChange_geometricallyIrreducible {k K : Type u} [Field k]
    [Finite k] [Field K] [Algebra k K]
    [GeometricallyIrreducible (FieldExtension.specMap k K)]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) [IsAbsolutelyQuasiSeparated X]
    (hX : IsScheme (baseChange (FieldExtension.specMap k K) X)) :
    IsScheme X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsScheme
