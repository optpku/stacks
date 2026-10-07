module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Normalization.Nagata

open AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 29.53.14: let `f : X ⟶ S` be a morphism. Assume that `S` is a
Nagata scheme, `f` is quasi-compact and quasi-separated, quasi-compact opens of `X` have finitely
many irreducible components, for every generic point `x` of an irreducible component of `X` the
residue-field extension `κ(x) / κ(f(x))` is finitely generated, and `X` is reduced. Then the
normalization `ν : S' ⟶ S` of `S` in `X`, formalized as `f.fromNormalization`, is finite. -/
@[stacks 0AVK]
#check (AlgebraicGeometry.Scheme.Hom.isFinite_fromNormalization_of_nagata :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    [Scheme.Nagata S] [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X] [IsReduced X],
    (∀ x : X, x ∈ genericPoints X →
      Algebra.FiniteType (S.residueField (f x)) (X.residueField x)) →
    IsFinite f.fromNormalization)
