/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Intersection.Number
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.AssociatedSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.Composition
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Intersections with effective Cartier divisors

Intersection with invertible modules on a closed subspace reduces to intersection
with the remaining factors on an effective Cartier divisor cut out by the first factor.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.Intersection

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/-- If the restriction of the first invertible module to a closed subspace of a proper
algebraic space is the sheaf associated to an effective Cartier divisor, the intersection
number equals the finite-difference intersection coefficient of the remaining factors
on that divisor. -/
theorem number_eq_tail_of_effectiveCartierDivisor
    {k : Type u} [Field k]
    {X Z D : AlgebraicSpace (Spec (CommRingCat.of k))} (i : Z ⟶ X)
    [IsClosedImmersion i] [Proper (SchemeRealization.toBase X)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z] [IsLocallyNoetherian D]
    {n : ℕ} (hZdim : dimension Z = n + 1)
    [Abelian X.Modules] [Abelian Z.Modules] [Abelian D.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions Z.Modules]
    [HasInjectiveResolutions D.Modules]
    (L : Fin (n + 1) → X.Modules) [∀ t : Fin (n + 1), isInvertibleObject (L t)]
    (j : D ⟶ Z) [IsEffectiveCartierDivisor j]
    (hL1 : (pullback i).obj (L 0) ≅ Hom.associatedSheaf j) :
    number i hZdim L = finiteDifferenceNumber (j ≫ i) (fun t : Fin n ↦ L t.succ) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.Intersection
