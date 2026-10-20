/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- For an affine morphism of schemes, pushforward of a quasicoherent module commutes with
tensoring by a quasicoherent module on the target. -/
theorem affineProjectionFormula
    {T S : Scheme.{u}} (h : T ⟶ S) [IsAffineHom h]
    (G : T.Modules) (H : S.Modules) [G.IsQuasicoherent] [H.IsQuasicoherent] :
    IsIsomorphic (((Scheme.Modules.pushforward h).obj G) ⊗ H)
      ((Scheme.Modules.pushforward h).obj (G ⊗ (Scheme.Modules.pullback h).obj H)) := sorry

end AlgebraicGeometry.Scheme.Modules
