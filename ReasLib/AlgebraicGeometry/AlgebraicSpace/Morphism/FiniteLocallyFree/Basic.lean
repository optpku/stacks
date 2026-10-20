/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine

/-!
# Finite locally free morphisms of algebraic spaces

A morphism of algebraic spaces is finite locally free when it is affine and the
direct image of its structure sheaf is a finite locally free module on the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces over `S` is finite locally free
if it is affine and `f_* 𝒪_X` is a finite locally free `𝒪_Y`-module. -/
class FiniteLocallyFree {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop extends Affine f where
  /-- The pushforward structure sheaf is finite locally free. -/
  pushforward_isFiniteLocallyFree :
    SheafOfModules.IsFiniteLocallyFree
      (Modules.pushforwardStructureModule f)

/-- The direct image of the structure module along a finite locally free
morphism is finite locally free. -/
instance FiniteLocallyFree.module_isFiniteLocallyFree {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [h : FiniteLocallyFree f] :
    SheafOfModules.IsFiniteLocallyFree
      (Modules.pushforwardStructureModule f) :=
  h.pushforward_isFiniteLocallyFree

/-- A morphism of algebraic spaces is finite locally free if and only if it is
affine and its pushforward structure sheaf is finite locally free. -/
theorem finiteLocallyFree_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    FiniteLocallyFree f ↔
      Affine f ∧ SheafOfModules.IsFiniteLocallyFree
        (Modules.pushforwardStructureModule f) :=
  sorry

namespace FiniteLocallyFree

/-- The identity morphism of an algebraic space is finite locally free. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : FiniteLocallyFree (𝟙 X) :=
  sorry

/-- An isomorphism of algebraic spaces is finite locally free. -/
instance of_isIso {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIso f] : FiniteLocallyFree f :=
  sorry

/-- The pushforward structure sheaf of a finite locally free morphism is
finite locally free. -/
@[reducible] def pushforwardStructureModule {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [h : FiniteLocallyFree f] :
    SheafOfModules.IsFiniteLocallyFree
      (Modules.pushforwardStructureModule f) :=
  h.pushforward_isFiniteLocallyFree

/-- A finite locally free morphism is affine and has finite locally free
pushforward structure sheaf. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteLocallyFree f] :
    Affine f ∧ SheafOfModules.IsFiniteLocallyFree
      (Hom.pushforwardStructureModule f) :=
  sorry

end FiniteLocallyFree

/-- Finite locally free morphisms of algebraic spaces are stable under composition. -/
instance finiteLocallyFree_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@FiniteLocallyFree S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composite of two finite locally free morphisms of algebraic spaces is
finite locally free. -/
instance finiteLocallyFree_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [FiniteLocallyFree f] [FiniteLocallyFree g] :
    FiniteLocallyFree (f ≫ g) :=
  MorphismProperty.comp_mem (@FiniteLocallyFree S) f g inferInstance inferInstance

end AlgebraicGeometry.AlgebraicSpace
