/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AssociatedCycle.ClosedSubspace
public import stacks_project.Chap82.Lemma_82_6_3_AssociatedCycle
import StacksCheckRecall

/-!
# Cycle of a closed subspace as a module cycle

In the good setup of Situation 82.2.1, the `k`-cycle of a closed subspace `Y ⊂ X`
equals the `k`-cycle of the pushforward `i_* 𝒪_Y` along the closed-immersion
inclusion `i = Y.ι`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The pushforward `i_* 𝒪_Y` of the structure module along a closed immersion is
a coherent `𝒪_X`-module on a locally Noetherian algebraic space. -/
def instIsCoherent_pushforward_unit {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (Y : ClosedSubspace X) :
    ((pushforward Y.ι).obj
        (SheafOfModules.unit (structureSheaf Y.X) : Y.X.Modules)).IsCoherent :=
  @Modules.ClosedImmersion.pushforward_unit_isCoherent S Y.X X
    inferInstance Y.ι Y.isClosedImmersion

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/- Lemma 82.6.3: In Situation 82.2.1, let `X / B` be good. Let `Y ⊂ X` be a closed
subspace. If `dim_δ(Y) ≤ k`, then `[Y]_k = [i_* 𝒪_Y]_k` where `i : Y ⟶ X` is the
inclusion morphism `Y.ι`. -/
@[stacks 0EED] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.closedSubspaceCycle_eq_moduleCycle_pushforward_unit :
    {S : Scheme.{u}} → {B X Z : AlgebraicSpace S} → [UniversallyCatenary B] →
    [IsAbsolutelyQuasiSeparated B] → (f : X ⟶ B) →
    [QuasiSeparated f] → [LocallyOfFiniteType f] → [IsLocallyNoetherian X] →
    (δ : Points B → ℤ) → [IsDimensionFunction δ] →
    (i : Z ⟶ X) → [IsClosedImmersion i] → (k : ℤ) →
    (hY : closedSubspaceDeltaDimension f δ (ClosedSubspace.ofι i) ≤ (k : EInt)) →
      closedSubspaceCycle f δ (ClosedSubspace.ofι i) k hY =
        moduleCycle f δ (Modules.pushforwardStructureModule i) k
          (moduleSupportDeltaDimension_pushforward_unit_le f δ i k hY))

end AlgebraicGeometry.AlgebraicSpace.Hom
