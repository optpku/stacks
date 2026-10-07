module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Support.IdealPower
import StacksCheckRecall

open AlgebraicGeometry

universe u

/-
Lemma 30.10.2: Let `X` be a Noetherian scheme, let `ℱ` be a coherent module on `X`, and let
`I` be the quasicoherent ideal sheaf defining a closed subscheme. Then `I ^ n ℱ = 0` for some
`n : ℕ` if and only if the support of `ℱ` is contained set-theoretically in the closed subscheme.
-/
@[stacks 01Y9] #check
  (AlgebraicGeometry.Scheme.Modules.exists_idealPowerProductSubobject_eq_bot_iff_moduleSupport_subset :
    ∀ {X : Scheme.{u}} [IsNoetherian X]
      (ℱ : X.Modules) [ℱ.IsCoherent] (I : X.IdealSheafData),
      (∃ n : ℕ,
        AlgebraicGeometry.Scheme.Modules.idealPowerProductSubobject I ℱ n = ⊥) ↔
        AlgebraicGeometry.RingedSpace.moduleSupport ℱ ⊆ (I.support : Set X))
