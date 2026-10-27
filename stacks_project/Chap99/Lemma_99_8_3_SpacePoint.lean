/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap99.«99_8_1_1_Functor»
public import stacks_project.Chap99.Lemma_99_7_5_SpacePoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.ProperSupport.SpacePoint

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

/- Proper-support quotient representatives over algebraic spaces are constructed
from epimorphisms with quasi-coherent finitely presented targets, flat over the
base and with proper support. -/
#check (AlgebraicGeometry.AlgebraicSpace.Quot.QuotSpacePoint.ofEpi :
  ∀ {S : Scheme.{u}} {X B T : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules)
    (h : T ⟶ B) [FinitePresentation f] (module : (pullback f h).Modules)
    (map : AlgebraicGeometry.AlgebraicSpace.Quot.spaceFiberF f F h ⟶ module),
    Epi map → module.IsQuasicoherent →
      Modules.flatOver module (pullback.snd f h) → module.IsFinitePresentation →
      AlgebraicGeometry.AlgebraicSpace.Quot.supportProperOver (pullback.snd f h) module →
        AlgebraicGeometry.AlgebraicSpace.Quot.QuotSpacePoint f F h)
