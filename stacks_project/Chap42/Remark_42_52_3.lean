/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.LocalizedChern.Mixed

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.LocalizedChern

universe u

/- Remark 42.52.3: In Situation 42.50.1, the mixed series
c⁽ᵖ⁾(Z ⟶ X, E) = 1 + c₁(E) + ⋯ + c_{p-1}(E) + c_p(Z ⟶ X, E) + c_{p+1}(Z ⟶ X, E) + ⋯
is the cutoff-valued family in A⁽ᵖ⁾(Z ⟶ X) with ambient Chern classes of E in
degrees n < p and localized Chern classes along Z ⟶ X in degrees n ≥ p. -/
@[stacks 0FBC] #check (AlgebraicGeometry.LocalizedChern.mixedChernClass :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (situation : Situation S δ X i E p .rankBound) (n : ℕ),
    BivariantClass.Cutoff δ (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) p n)
