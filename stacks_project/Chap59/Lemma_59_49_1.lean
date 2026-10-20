/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.LowerShriek
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.StandardTopology.Big

universe u

/- Lemma 59.49.1 (1): inverse image on additive sheaves over a standard big site has the
standard additive lower-shriek functor as a left adjoint. -/
@[stacks 04CC]
#check (AlgebraicGeometry.StandardTopology.Big.additiveLowerShriekAdjunction :
  ∀ (τ : StandardTopology) {X Y : Scheme.{u}} (f : X ⟶ Y),
    AlgebraicGeometry.StandardTopology.Big.additiveLowerShriek τ f ⊣
      AlgebraicGeometry.StandardTopology.Big.additiveInverseImage τ f)

/- Lemma 59.49.1 (2): additive lower shriek over a standard big site is exact. -/
@[stacks 04CC]
#check (AlgebraicGeometry.StandardTopology.Big.additiveLowerShriek_exact :
  ∀ (τ : StandardTopology) {X Y : Scheme.{u}} (f : X ⟶ Y),
    exactFunctor
      (Sheaf (τ.overTopology X) AddCommGrpCat.{u + 1})
      (Sheaf (τ.overTopology Y) AddCommGrpCat.{u + 1})
      (AlgebraicGeometry.StandardTopology.Big.additiveLowerShriek τ f))

/- Lemma 59.49.1 (3): inverse image on modules over a standard big ringed site has the
standard module lower-shriek functor as a left adjoint. -/
@[stacks 04CC]
#check (AlgebraicGeometry.StandardTopology.Big.moduleLowerShriekAdjunction :
  ∀ (τ : StandardTopology) {X Y : Scheme.{u}} (f : X ⟶ Y),
    AlgebraicGeometry.StandardTopology.Big.moduleLowerShriek τ f ⊣
      AlgebraicGeometry.StandardTopology.Big.modulePullback τ f)

/- Lemma 59.49.1 (4): module lower shriek over a standard big ringed site is exact. -/
@[stacks 04CC]
#check (AlgebraicGeometry.StandardTopology.Big.moduleLowerShriek_exact :
  ∀ (τ : StandardTopology) {X Y : Scheme.{u}} (f : X ⟶ Y),
    exactFunctor
      (SheafOfModules.{u + 1} (structureSheaf τ X))
      (SheafOfModules.{u + 1} (structureSheaf τ Y))
      (AlgebraicGeometry.StandardTopology.Big.moduleLowerShriek τ f))

/- Lemma 59.49.1 (5): additive and module lower shriek agree on underlying additive
sheaves. -/
@[stacks 04CC]
#check (AlgebraicGeometry.StandardTopology.Big.underlyingComparison_isIso :
  ∀ (τ : StandardTopology) {X Y : Scheme.{u}} (f : X ⟶ Y),
    IsIso (AlgebraicGeometry.StandardTopology.Big.underlyingComparison τ f))
