module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.FieldTheory.RatFunc.FieldExtension
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Rational-function invariance of geometric irreducibility

The one-variable rational-function extension is a reusable field-extension operation.  The
criterion is stated at the canonical `Spec.map` level, with the named algebra owner exposed by
the neutral `RatFunc.FieldExtension` support module; tensor/localization transport belongs in
proof-support leaves rather than in the public chapter surface.
-/

@[expose] public section

open AlgebraicGeometry
open scoped RatFunc

universe u

namespace AlgebraicGeometry.FieldExtension.GeometricallyIrreducible.RatFunc

/-- The scheme morphism induced by the canonical coefficient extension `k(X) → K(X)`. -/
@[stacks 0G31 "canonical rational-function spectrum map"]
noncomputable def specMap
    {k K : Type u} [Field k] [Field K] [Algebra k K] :
    Spec (CommRingCat.of (RatFunc K)) ⟶ Spec (CommRingCat.of (RatFunc k)) :=
  Spec.map (CommRingCat.ofHom (RatFunc.FieldExtension.map (k := k) (K := K)))

/-- The named rational-function algebra owner agrees with the map used by `specMap`. -/
theorem specMap_eq_algebraMap
    {k K : Type u} [Field k] [Field K] [Algebra k K] :
    specMap (k := k) (K := K) =
      Spec.map (CommRingCat.ofHom
        (@algebraMap (RatFunc k) (RatFunc K) _ _
          (RatFunc.FieldExtension.algebra (k := k) (K := K)))) := sorry

/-- Lemma 10.47.10 (Tag 0G31): geometric irreducibility is unchanged by adjoining one rational
function variable to both fields. -/
@[stacks 0G31]
theorem iff
    {k K : Type u} [Field k] [Field K] [Algebra k K] :
    GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap k K))) ↔
      GeometricallyIrreducible (specMap (k := k) (K := K)) := sorry

/-- The rational-function criterion in the explicit algebra-map `Spec.map` spelling. -/
@[stacks 0G31]
theorem iff_algebraMap
    {k K : Type u} [Field k] [Field K] [Algebra k K] :
    GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap k K))) ↔
      GeometricallyIrreducible
        (Spec.map (CommRingCat.ofHom
          (@algebraMap (RatFunc k) (RatFunc K) _ _
            (RatFunc.FieldExtension.algebra (k := k) (K := K))))) := sorry

end AlgebraicGeometry.FieldExtension.GeometricallyIrreducible.RatFunc
