/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Length
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Stalk

/-!
# Geometric-stalk length of modules on algebraic spaces

For quasi-coherent modules, geometric-stalk length agrees with Zariski-stalk length on
étale scheme charts and depends only on the underlying point of the algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The length of an `𝒪_X`-module at a geometric point `xbar`, as the module length of the
étale stalk `stalkModuleCat xbar F` over `etaleLocalRing X xbar`. -/
def lengthAtGeometricPoint (F : X.Modules) (xbar : GeometricPoint X) : ℕ∞ :=
  Module.length (etaleLocalRing X xbar) (stalkModuleCat xbar F)

/-- `lengthAtGeometricPoint F xbar` is the module length of the étale stalk of `F` at `xbar`. -/
theorem lengthAtGeometricPoint_eq (F : X.Modules) (xbar : GeometricPoint X) :
    lengthAtGeometricPoint F xbar =
      Module.length (etaleLocalRing X xbar) (stalkModuleCat xbar F) :=
  rfl

/-- For a quasi-coherent module, the étale-stalk length at `xbar` equals the Zariski-stalk
length of `F` on any étale scheme chart whose image point is `xbar.image`. -/
theorem lengthAtGeometricPoint_eq_lengthOnEtaleChart (F : X.Modules) [F.IsQuasicoherent]
    (xbar : GeometricPoint X) {U : Over S} (φ : ofOver U ⟶ X) [Etale φ] {u : U.left}
    (hu : Points.mapOfOver φ u = xbar.image) :
    lengthAtGeometricPoint F xbar = lengthOnEtaleChart φ F u :=
  sorry

/-- For a quasi-coherent module, étale-stalk length depends only on the image point of the
geometric point in `|X|`. -/
theorem lengthAtGeometricPoint_eq_of_liesOver (F : X.Modules) [F.IsQuasicoherent]
    {xbar ybar : GeometricPoint X} (h : xbar.image = ybar.image) :
    lengthAtGeometricPoint F xbar = lengthAtGeometricPoint F ybar :=
  sorry

/-- For a quasi-coherent module and a geometric point over `x`, geometric-stalk length equals
`d` if and only if some, equivalently every, étale scheme chart at a point over `x` has
Zariski-stalk length `d`. -/
theorem lengthAt_tfae (F : X.Modules) [F.IsQuasicoherent] (x : Points X)
    (xbar : GeometricPoint X) (hx : xbar.liesOver x) (d : ℕ∞) :
    List.TFAE
      [lengthAtGeometricPoint F xbar = d,
        ∃ (U : Over S) (φ : ofOver U ⟶ X),
          Etale φ ∧ ∃ u : U.left,
            Points.mapOfOver φ u = x ∧ lengthOnEtaleChart φ F u = d,
        ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ] (u : U.left),
          Points.mapOfOver φ u = x → lengthOnEtaleChart φ F u = d] :=
  sorry

/-- The étale-stalk length of a quasi-coherent module at some geometric point over `x` equals
`d` if and only if some étale scheme chart over `x` has Zariski-stalk length `d`. -/
theorem exists_lengthAtGeometricPoint_iff (F : X.Modules) [F.IsQuasicoherent]
    (x : Points X) (d : ℕ∞) :
    (∃ xbar : GeometricPoint X, xbar.liesOver x ∧ lengthAtGeometricPoint F xbar = d) ↔
      ∃ (U : Over S) (φ : ofOver U ⟶ X),
        Etale φ ∧ ∃ u : U.left,
          Points.mapOfOver φ u = x ∧ lengthOnEtaleChart φ F u = d :=
  sorry

/-- Some étale scheme chart over `x` has Zariski-stalk length `d` if and only if every étale
scheme chart over `x` has Zariski-stalk length `d`. -/
theorem exists_lengthOnEtaleChart_iff_forall (F : X.Modules) [F.IsQuasicoherent]
    (x : Points X) (d : ℕ∞) :
    (∃ (U : Over S) (φ : ofOver U ⟶ X),
        Etale φ ∧ ∃ u : U.left,
          Points.mapOfOver φ u = x ∧ lengthOnEtaleChart φ F u = d) ↔
      ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ] (u : U.left),
        Points.mapOfOver φ u = x → lengthOnEtaleChart φ F u = d :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
