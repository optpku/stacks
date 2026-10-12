/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_49_1_FiniteComponents
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_49_3
import StacksCheckRecall

/-!
# Finite irreducible components along flat locally finite type morphisms

A flat morphism of algebraic spaces that is locally of finite type pulls back
the equivalent conditions of Lemma 67.49.1 from the target to the source, and
sends codimension-`0` points to codimension-`0` points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace HasFiniteIrreducibleComponentsOnCompactOpens

/-- Lemma 67.49.4 (1): let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `f` is flat and locally of finite type and `Y`
satisfies the equivalent conditions of Lemma 67.49.1, recorded as
`HasFiniteIrreducibleComponentsOnCompactOpens Y`, then `X` satisfies those
equivalent conditions. -/
@[stacks 0GMD]
theorem of_flat_locallyOfFiniteType {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFiniteType f]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y] :
    HasFiniteIrreducibleComponentsOnCompactOpens X :=
  sorry

end HasFiniteIrreducibleComponentsOnCompactOpens

/- Lemma 67.49.4 (2): under the same hypotheses, if `x` has codimension `0` in
`X` then `f(x)` has codimension `0` in `Y`. A point of codimension `0` means
`localRingDimAt _ = 0`, and `f(x)` is `Points.map f x`. This is the canonical
lemma `Flat.localRingDimAt_map_eq_zero`, which needs only `[Flat f]`. -/
@[stacks 0GMD]
#check (Flat.localRingDimAt_map_eq_zero :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Flat f]
    {x : Points X}, localRingDimAt x = 0 →
    localRingDimAt (Points.map f x) = 0)

end AlgebraicGeometry.AlgebraicSpace
