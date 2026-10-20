/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Module.Descent.Fpqc
public import ReasLib.AlgebraicGeometry.Scheme.Module.Descent.GaloisCover

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.QCoh.GaloisDescent

variable {G : Type v} [Group G] [Finite G] {X Y : Scheme.{u}} (p : X ⟶ Y)
variable (rho : Gᵐᵒᵖ →* Aut (Over.mk p : Over Y))

/-- For a surjective finite étale morphism whose orbit map is an isomorphism,
pullback to the category of equivariant quasi-coherent modules is an equivalence. -/
instance descentIsEquivalence [IsFinite p] [Etale p] [Surjective p]
    [IsIso (orbitMap p rho)] : (descent p rho).IsEquivalence := sorry

end AlgebraicGeometry.Scheme.QCoh.GaloisDescent
