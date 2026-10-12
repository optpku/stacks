/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition

/-!
# Stalkwise free module sheaves

This leaf owns the pointwise freeness condition for module sheaves on a ringed space.  It is
independent of local-ring hypotheses, finite-generation conditions, and quasi-coherence.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Modules

variable {X : RingedSpace.{u}}

/-- A module sheaf is stalkwise free when its stalk at every point is a free module over the
corresponding stalk of the structure sheaf. -/
class IsStalkwiseFree (ℱ : X.Modules) : Prop where
  /-- The freeness of the stalk at a chosen point. -/
  stalk_free (x : X) :
    Module.Free (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x)

/-- Stalkwise freeness is precisely the pointwise freeness condition on bundled stalk modules. -/
theorem isStalkwiseFree_iff (ℱ : X.Modules) :
    IsStalkwiseFree ℱ ↔
      ∀ x : X, Module.Free (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) := sorry

/-- A stalkwise-free module supplies free stalks as typeclass instances. -/
instance instModuleFreeStalkOfIsStalkwiseFree
    {ℱ : X.Modules} [IsStalkwiseFree ℱ] (x : X) :
    Module.Free (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) := sorry

end AlgebraicGeometry.RingedSpace.Modules
