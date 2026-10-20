/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocalizedChern.Mixed
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import stacks_project.Chap42.Remark_42_34_7_Cutoff
public import stacks_project.Chap42.Definition_42_50_3_LocalizedClasses

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/- Compatibility: the mixed Chern series in the cutoff family. -/
#check (AlgebraicGeometry.LocalizedChern.mixedChernClass :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (situation : Situation S δ X i E p .rankBound) (n : ℕ),
    BivariantClass.Cutoff δ (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) p n)

end AlgebraicGeometry.LocalizedChern
