/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.SimplicialScheme.Module.Pullback
public import ReasLib.AlgebraicTopology.SimplicialObject.Cartesian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Pushforward of quasi-coherent modules on simplicial schemes

Pushforward along a cartesian morphism with quasi-compact and quasi-separated
components preserves quasi-coherence when the target face maps are flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.SimplicialObject

/-- Pushforward along a cartesian morphism of simplicial schemes with quasi-compact
and quasi-separated components preserves quasi-coherent modules if all face maps
of the target are flat. -/
instance modulePushforward_isQuasicoherent {V U : SimplicialObject Scheme.{u}}
    (f : V ⟶ U) [CategoryTheory.SimplicialObject.IsCartesian f]
    [∀ (n : ℕ) (j : Fin (n + 2)), Flat (U.δ j)]
    [∀ (n : ℕ), QuasiCompact (f.app (op ⦋n⦌))]
    [∀ (n : ℕ), QuasiSeparated (f.app (op ⦋n⦌))]
    (G : SheafOfModules.{u} (structureSheaf V))
    [G.IsQuasicoherent] :
    ((SheafOfModules.pushforward.{u} (structureSheafMap f)).obj G).IsQuasicoherent :=
  sorry

end AlgebraicGeometry.SimplicialObject
