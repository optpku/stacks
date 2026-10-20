/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowMotive.Duality
public import ReasLib.AlgebraicGeometry.ChowMotive.Representability

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Correspondence
open scoped CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace ChowMotive

/-- A morphism of rational Chow motives is an isomorphism if, after tensoring with
the motive of every smooth projective scheme, it induces an isomorphism on every
degreewise group of the concrete rational Chow realization. -/
theorem isIso_of_chowTensor {k : Type u} [Field k]
    {M N : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)} (c : M ⟶ N)
    (h_chow : ∀ (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom] (i : ℤ),
      IsIso ((chowFunctor (k := k) i).map (c ⊗ₘ 𝟙 (ChowMotive.h X)))) :
    IsIso c := sorry

end ChowMotive
