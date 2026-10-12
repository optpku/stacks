/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.Affine
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 31.12.2: let `X` be an integral locally Noetherian scheme and let `ℱ` be a coherent
`𝒪_X`-module. Then `ℱ` is reflexive if and only if, for every affine open `U ⊆ X`, the module
of sections `Γ(ℱ, U)` is reflexive over `Γ(X, U)`. -/
@[stacks 0AY0] #check
  (AlgebraicGeometry.Scheme.Modules.isReflexive_iff_affineOpen :
    ∀ {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
      (ℱ : X.Modules) [ℱ.IsCoherent],
      AlgebraicGeometry.Scheme.Modules.IsReflexive ℱ ↔
        ∀ U : X.Opens, IsAffineOpen U → Module.IsReflexive (Γ(X, U)) (Γ(ℱ, U)))
