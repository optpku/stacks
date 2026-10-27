/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.LocallyQuasiCoherent
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module.Comparison

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- A locally quasi-coherent étale module on an algebraic stack is an fppf sheaf
if its canonical small-étale comparison maps are isomorphisms along morphisms
lying over flat, locally finitely presented morphisms of schemes. -/
theorem isSheaf_fppf_of_isLocallyQuasiCoherent
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) [IsLocallyQuasiCoherent F]
    (h_comparison : ∀ {x y : X.total} (φ : x ⟶ y),
      Flat (X.p.map φ).left → LocallyOfFinitePresentation (X.p.map φ).left →
        IsIso (moduleComparison φ F)) :
    Presheaf.IsSheaf X.fppfTopology F.val.presheaf := sorry

end AlgebraicGeometry.GroupoidsOver
