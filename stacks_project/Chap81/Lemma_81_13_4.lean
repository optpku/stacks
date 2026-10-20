/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing.Factorization
import StacksCheckRecall

/-!
# Lemma 81.13.4

In Situation 81.13.2 with `X` quasi-compact, the sequential coequalizer system
of 81.13.3.1 is eventually factorable through a closed immersion of the ambient
space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing

/- Lemma 81.13.4: in Situation 81.13.2 with `X` quasi-compact, the sequential
coequalizer system of 81.13.3.1 is eventually factorable: for all `n` large enough
there exists `m` such that the transition map `X_n ⟶ X_{n + m}` factors through a
closed immersion `X ⟶ X_{n + m}`. The Lean object `(system f i h_iso).obj n` is the
Stacks stage `X_{n+1}`. -/
@[stacks 0AGK] #check
  (AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing.systemMap_eventually_factorsThrough_closedImmersion :
    ∀ {S : Scheme.{u}} {X X' Z : AlgebraicSpace S}
    (f : X' ⟶ X) (i : Z ⟶ X) [IsLocallyNoetherian X] [IsQuasiCompact X]
    [IsClosedImmersion i] [Proper f]
    (h_iso : IsIsoOverOpen f (closedImmersionComplementι i)),
    ∃ N : ℕ, ∀ n, N ≤ n → ∃ m : ℕ, ∃ (ι : X ⟶ (system f i h_iso).obj (n + m)),
      IsClosedImmersion ι ∧
        (system f i h_iso).map (homOfLE (n.le_add_right m)) =
          toAmbient f i h_iso n ≫ ι)

/- The witnessing closed immersion in
`systemMap_eventually_factorsThrough_closedImmersion` may be taken as a section of
the structure morphism `toAmbient`. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing.systemMap_eventually_factorsThrough_closedImmersion_section :
    ∀ {S : Scheme.{u}} {X X' Z : AlgebraicSpace S}
    (f : X' ⟶ X) (i : Z ⟶ X) [IsLocallyNoetherian X] [IsQuasiCompact X]
    [IsClosedImmersion i] [Proper f]
    (h_iso : IsIsoOverOpen f (closedImmersionComplementι i)),
    ∃ N : ℕ, ∀ n, N ≤ n → ∃ m : ℕ, ∃ (ι : X ⟶ (system f i h_iso).obj (n + m)),
      IsClosedImmersion ι ∧
        (system f i h_iso).map (homOfLE (n.le_add_right m)) =
          toAmbient f i h_iso n ≫ ι ∧
        ι ≫ toAmbient f i h_iso (n + m) = 𝟙 X)

end AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing
