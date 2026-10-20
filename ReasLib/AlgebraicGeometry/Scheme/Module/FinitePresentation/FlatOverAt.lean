/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import ReasLib.Algebra.Module.FinitePresentation.Descent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.EtaleNeighborhood

/-!
# Finite presentation of a stalk from flatness at a point

A finite-type quasicoherent module that is flat over a locally finitely presented
morphism at a point has a finitely presented stalk at that point.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite-type quasicoherent module that is flat over a locally finitely presented
morphism at a point has a finitely presented stalk at that point. -/
@[stacks 05I7]
theorem stalkFinitePresentationOfFlatOverAt
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (x : X) (h_flat : flatOverAt F f x) :
    Module.FinitePresentation (X.presheaf.stalk x)
      (RingedSpace.stalkModuleCat F x) := sorry

set_option synthInstance.checkSynthOrder false in
/-- Flatness at a point supplies the canonical finite-presentation instance for the stalk of a
finite-type quasicoherent module over a locally finitely presented morphism. -/
instance instStalkFinitePresentationOfFlatOverAt
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (x : X) [h_flat : flatOverAt F f x] :
    Module.FinitePresentation (X.presheaf.stalk x)
      (RingedSpace.stalkModuleCat F x) :=
  stalkFinitePresentationOfFlatOverAt f F x h_flat

end AlgebraicGeometry.Scheme.Modules
