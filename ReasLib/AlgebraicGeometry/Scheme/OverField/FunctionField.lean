module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety

/-!
# Function fields of varieties over a field

The function field itself is owned by `Scheme`.  This leaf records the scalar
structure induced by a chosen map to `Spec k`; it is explicit because the
carrier `X.left.functionField` alone does not remember that structure map.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- The structural map `k → k(X)` induced by a variety `X` over `k`. -/
@[stacks 0BXN "function-field structural map"]
noncomputable def functionFieldAlgebraMap
    (X : SchemeOverField k) [Variety X] :
    k →+* X.left.functionField :=
  (X.hom.stalkMap (genericPoint X.left)).hom.comp
    (StructureSheaf.toStalk k (X.hom (genericPoint X.left))).hom

/-- The canonical `k`-algebra structure on the function field of a variety over `k`.

It is an explicit owner rather than a global instance because the underlying
function-field carrier does not determine the chosen structure morphism. -/
@[reducible, stacks 0BXN "function-field algebra structure"]
noncomputable def functionFieldAlgebra
    (X : SchemeOverField k) [Variety X] :
    Algebra k X.left.functionField :=
  (functionFieldAlgebraMap X).toAlgebra

/-- The function field of a variety over `k`, packaged as a commutative `k`-algebra. -/
@[stacks 0BXN "bundled function-field algebra"]
noncomputable def functionFieldCommAlg
    (X : SchemeOverField k) [Variety X] : CommAlgCat k :=
  @CommAlgCat.of k _ X.left.functionField _ (functionFieldAlgebra X)

/-- The function field of a variety over `k` is essentially of finite type over `k`. -/
@[instance]
theorem functionField_essFiniteType (X : SchemeOverField k) [Variety X] :
    Algebra.EssFiniteType k (functionFieldCommAlg X) := sorry

/-- The dimension of a variety over a field equals the transcendence degree of its
function field with the canonical scalar structure. -/
@[stacks 06A1]
theorem topologicalKrullDim_eq_trdeg_functionField
    {k : Type u} [Field k] (X : SchemeOverField k) [Variety X] :
    topologicalKrullDim X.left =
      (Cardinal.toNat (Algebra.trdeg k (functionFieldCommAlg X)) : WithBot ℕ∞) := sorry

end AlgebraicGeometry.SchemeOverField
