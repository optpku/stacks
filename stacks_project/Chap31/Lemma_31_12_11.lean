/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.Depth
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped ENat

universe u

/- Lemma 31.12.11 (1): let `X` be an integral locally Noetherian scheme, let `ℱ` be a coherent
reflexive `𝒪_X`-module, and let `x : X`. If the depth of the local ring at `x` is at least two,
then the depth of the stalk `ℱ_x` is at least two. -/
@[stacks 0EBI] #check (
  AlgebraicGeometry.Scheme.Modules.IsReflexive.moduleDepth_stalk_ge_two_of_ringDepth_stalk_ge_two :
    ∀ {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
      (ℱ : X.Modules) [ℱ.IsCoherent]
      [AlgebraicGeometry.Scheme.Modules.IsReflexive ℱ] (x : X),
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x) →
        (2 : ℕ∞) ≤
          moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x))

/- Lemma 31.12.11 (2): let `X` be an integral locally Noetherian scheme and let `ℱ` be a
coherent reflexive `𝒪_X`-module. If `X` satisfies `(S₂)`, then `ℱ` satisfies `(S₂)`. -/
@[stacks 0EBI] #check (
  AlgebraicGeometry.Scheme.Modules.IsReflexive.satisfiesSerreConditionS_two :
    ∀ {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
      (ℱ : X.Modules) [ℱ.IsCoherent]
      [AlgebraicGeometry.Scheme.Modules.IsReflexive ℱ],
      AlgebraicGeometry.Scheme.satisfiesSerreConditionS X 2 →
        AlgebraicGeometry.Scheme.Modules.satisfiesSerreConditionS ℱ 2)
