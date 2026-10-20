/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing

/-!
# Eventual closed-immersion factorization of coequalizer glueing systems
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing

variable {S : Scheme.{u}} {X X' Z : AlgebraicSpace S}

/-- For a proper morphism that is an isomorphism away from a closed subspace of
a quasi-compact locally Noetherian algebraic space, every sufficiently late
stage of the infinitesimal-neighbourhood coequalizer system has a transition
factoring through a closed immersion of the ambient space. -/
@[stacks 0AGK]
theorem systemMap_eventually_factorsThrough_closedImmersion
    (f : X' ⟶ X) (i : Z ⟶ X) [IsLocallyNoetherian X] [IsQuasiCompact X]
    [IsClosedImmersion i] [Proper f]
    (h_iso : IsIsoOverOpen f (closedImmersionComplementι i)) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∃ m : ℕ, ∃ (ι : X ⟶ (system f i h_iso).obj (n + m)),
      IsClosedImmersion ι ∧
        (system f i h_iso).map (homOfLE (n.le_add_right m)) =
          toAmbient f i h_iso n ≫ ι :=
  sorry

/-- For a proper morphism that is an isomorphism away from a closed subspace of
a quasi-compact locally Noetherian algebraic space, every sufficiently late
stage of the infinitesimal-neighbourhood coequalizer system has a transition
factoring through a closed immersion of the ambient space that is a section
of the later structure morphism. -/
theorem systemMap_eventually_factorsThrough_closedImmersion_section
    (f : X' ⟶ X) (i : Z ⟶ X) [IsLocallyNoetherian X] [IsQuasiCompact X]
    [IsClosedImmersion i] [Proper f]
    (h_iso : IsIsoOverOpen f (closedImmersionComplementι i)) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∃ m : ℕ, ∃ (ι : X ⟶ (system f i h_iso).obj (n + m)),
      IsClosedImmersion ι ∧
        (system f i h_iso).map (homOfLE (n.le_add_right m)) =
          toAmbient f i h_iso n ≫ ι ∧
        ι ≫ toAmbient f i h_iso (n + m) = 𝟙 X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing
