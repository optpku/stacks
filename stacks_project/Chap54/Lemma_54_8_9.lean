/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.PointBlowupSequence.DualizingModule

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 54.8.9: the differential determinant of a finite closed-point blowup sequence maps to a
dualizing module, extending its generic-point identification. -/
@[stacks 0B4T] #check
  (AlgebraicGeometry.Scheme.PointBlowupSequence.exists_map_toDualizingModule :
    ∀ (p : ℕ) (hp : p.Prime) (A₀ A : Type u) [CommRing A₀] [CommRing A]
      [Algebra A₀ A],
      Function.Injective (algebraMap A₀ A) → [IsRegularLocalRing A] → [CharP A p] →
      ringKrullDim A = 2 → ∀ (r : ℕ) [Module.Free A Ω[A⁄A₀]] [Module.Finite A Ω[A⁄A₀]],
      Module.finrank A Ω[A⁄A₀] = r → ∀ {X : Scheme.{u}},
      (s : AlgebraicGeometry.Scheme.PointBlowupSequence (Spec (.of A)) X) →
    let S := Spec (.of A)
    let f₀ := Spec.map (CommRingCat.ofHom (algebraMap A₀ A))
    let ωA := (ModuleCat.of A Ω[A⁄A₀]).exteriorPower r
    let ωS := Λ[r] Ω[f₀.toShHom]
    let ωX :=
      AlgebraicGeometry.Scheme.PointBlowupSequence.canonicalModule s ωS
    let ΩrX := AlgebraicGeometry.Scheme.Modules.ReflexiveDeterminant.sheaf r
      Ω[(s.toSource ≫ f₀).toShHom]
    let d := AlgebraicGeometry.Scheme.RelativeDifferentials.reflexiveDeterminantComparison
      s.toSource f₀ r
    let c := AlgebraicGeometry.Scheme.PointBlowupSequence.canonicalMap s ωS
    ∃ φ : ΩrX ⟶ ωX, ∀ η : genericPoints X,
      RingedSpace.moduleStalkHom η.1 d ≫ RingedSpace.moduleStalkHom η.1 φ =
        RingedSpace.moduleStalkHom η.1 c)
