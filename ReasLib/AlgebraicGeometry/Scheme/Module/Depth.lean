/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.Depth
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent

/-!
# Stalkwise depth conditions for coherent scheme modules

This leaf supplies the locally Noetherian scheme specialization of the
locally-ringed-space depth API. It is the owner for the finite-stalk bridge
from finite presentation and for the familiar coherent-module spelling of
Serre's condition `(S_k)`.
-/

@[expose] public section

open AlgebraicGeometry
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- A finitely presented module on a locally Noetherian scheme has finite stalks. -/
theorem hasFiniteStalks_of_isFinitePresentation
    (ℱ : X.Modules) [ℱ.IsFinitePresentation] :
    LocallyRingedSpace.Modules.HasFiniteStalks
      (X := X.toLocallyRingedSpace) ℱ := sorry

/-- Finite presentation supplies the generic finite-stalks instance on a locally Noetherian
scheme. -/
instance instHasFiniteStalksOfIsFinitePresentation
    (ℱ : X.Modules) [ℱ.IsFinitePresentation] :
    LocallyRingedSpace.Modules.HasFiniteStalks
      (X := X.toLocallyRingedSpace) ℱ :=
  hasFiniteStalks_of_isFinitePresentation ℱ

/-- A coherent module on a locally Noetherian scheme has finite stalks. -/
instance instHasFiniteStalksOfIsCoherent
    (ℱ : X.Modules) [ℱ.IsCoherent] :
    LocallyRingedSpace.Modules.HasFiniteStalks
      (X := X.toLocallyRingedSpace) ℱ :=
  hasFiniteStalks_of_isFinitePresentation ℱ

/-- A coherent scheme module has depth `k` at `x` when its stalk has
depth `k` over the local stalk ring. -/
abbrev hasDepthAt
    (ℱ : X.Modules) [ℱ.IsCoherent] (x : X) (k : ℕ) : Prop :=
  LocallyRingedSpace.Modules.hasDepthAt
    (X := X.toLocallyRingedSpace) ℱ x k

/-- The coherent scheme-module depth predicate unfolds to the depth of its stalk. -/
theorem hasDepthAt_def
    (ℱ : X.Modules) [ℱ.IsCoherent] (x : X) (k : ℕ) :
    hasDepthAt ℱ x k =
      (moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) = k) := sorry

/-- The coherent scheme-module depth predicate is equivalent to the corresponding stalk-depth
equality. -/
@[simp]
theorem hasDepthAt_iff
    (ℱ : X.Modules) [ℱ.IsCoherent] (x : X) (k : ℕ) :
    hasDepthAt ℱ x k ↔
      moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) = k := sorry

/-- A coherent scheme module satisfies `(S_k)` when every stalk has
the required local depth lower bound. -/
abbrev satisfiesSerreConditionS
    (ℱ : X.Modules) [ℱ.IsCoherent] (k : ℕ) : Prop :=
  LocallyRingedSpace.Modules.satisfiesSerreConditionS
    (X := X.toLocallyRingedSpace) ℱ k

/-- The coherent scheme-module Serre condition unfolds to its stalkwise depth inequalities. -/
theorem satisfiesSerreConditionS_def
    (ℱ : X.Modules) [ℱ.IsCoherent] (k : ℕ) :
    satisfiesSerreConditionS ℱ k =
      (∀ x : X,
        WithBot.some (moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) : ℕ∞) ≥
          min (k : WithBot ℕ∞)
            (Module.supportDim (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x))) := sorry

/-- The coherent scheme-module Serre condition is equivalent to its stalkwise depth
inequalities. -/
@[simp]
theorem satisfiesSerreConditionS_iff
    (ℱ : X.Modules) [ℱ.IsCoherent] (k : ℕ) :
    satisfiesSerreConditionS ℱ k ↔
      ∀ x : X,
        WithBot.some (moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) : ℕ∞) ≥
          min (k : WithBot ℕ∞)
            (Module.supportDim (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x)) := sorry

end AlgebraicGeometry.Scheme.Modules
