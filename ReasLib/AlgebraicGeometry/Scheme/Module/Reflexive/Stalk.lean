/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.LinearAlgebra.Dual.Defs
public import ReasLib.AlgebraicGeometry.Noetherian.ClosedPoints
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive
import Mathlib.Tactic.CrossRefAttribute

/-!
# Reflexivity of stalks

This file relates reflexivity of a coherent module sheaf to reflexivity of its stalks.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
variable (ℱ : X.Modules) [ℱ.IsCoherent]

/-- A coherent module sheaf on an integral locally Noetherian scheme is reflexive if and only if
all of its stalks are reflexive, and it suffices to test this at closed points. -/
@[stacks 0AY3]
theorem isReflexive_tfae_stalk_and_closedPointStalk :
    List.TFAE
      [ IsReflexive ℱ
      , ∀ x : X, Module.IsReflexive (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x)
      , ∀ x : X, x ∈ closedPoints X →
          Module.IsReflexive (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x)
      ] := sorry

end AlgebraicGeometry.Scheme.Modules
