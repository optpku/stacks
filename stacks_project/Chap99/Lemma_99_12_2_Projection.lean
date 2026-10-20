/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap99.Lemma_99_12_1_Graph

/-!
# First projection of a Hilbert fibre point

A closed subspace `Y ⊂ (Z ×_B X)_T` that is of finite presentation, flat, and
proper over `T` has a first-projection restriction `pr₁|_Y : Y ⟶ Z_T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace.Quot (SchemesOver)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

variable {S : Scheme.{u}} {Z B X : AlgebraicSpace S}

/-- The two maps `Y ⟶ T` and `Y ⟶ Z` from a fibre point agree over `B`. -/
theorem fstRestrict_lift_condition {z : Z ⟶ B} {x : X ⟶ B} {σ : SchemesOver B}
    (p : FiberPoint z x σ) :
    p.structureMap ≫ σ.hom =
      (p.subspace.ι ≫ pullback.fst (productHom z x) σ.hom ≫ pullback.fst z x) ≫ z :=
  sorry

/-- The first-projection restriction `k = pr₁|_Y : Y ⟶ Z_T` of a fibre point. -/
def fstRestrict {z : Z ⟶ B} {x : X ⟶ B} {σ : SchemesOver B}
    (p : FiberPoint z x σ) : p.subspace.X ⟶ pullback σ.hom z :=
  pullback.lift p.structureMap
    (p.subspace.ι ≫ pullback.fst (productHom z x) σ.hom ≫ pullback.fst z x)
    (fstRestrict_lift_condition p)

/-- The composite of `fstRestrict` with the projection `Z_T ⟶ T` is the
structure morphism of `Y`. -/
theorem fstRestrict_fst {z : Z ⟶ B} {x : X ⟶ B} {σ : SchemesOver B}
    (p : FiberPoint z x σ) :
    fstRestrict p ≫ pullback.fst σ.hom z =
      p.subspace.ι ≫ pullback.snd (productHom z x) σ.hom :=
  sorry

/-- The composite of `fstRestrict` with the projection `Z_T ⟶ Z` is the
composite of the closed immersion of `Y` with the projections of
`(Z ×_B X)_T` to `Z`. -/
theorem fstRestrict_snd {z : Z ⟶ B} {x : X ⟶ B} {σ : SchemesOver B}
    (p : FiberPoint z x σ) :
    fstRestrict p ≫ pullback.snd σ.hom z =
      p.subspace.ι ≫ pullback.fst (productHom z x) σ.hom ≫ pullback.fst z x :=
  sorry

/-- The structure morphism of a fibre point factors as `fstRestrict` followed
by the projection `Z_T ⟶ T`. -/
theorem fstRestrict_comp_structureMap {z : Z ⟶ B} {x : X ⟶ B} {σ : SchemesOver B}
    (p : FiberPoint z x σ) :
    fstRestrict p ≫ pullback.fst σ.hom z = p.structureMap :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
