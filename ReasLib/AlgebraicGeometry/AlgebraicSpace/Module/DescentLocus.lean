/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Hom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

/-!
# Descent locus of a finite locally free module on algebraic spaces

A morphism `g : Y' ⟶ Y` lies in the descent locus of a finite locally free
`𝒪_X`-module `E` along `f : X ⟶ Y` when `(g')^* E` is the pullback of some
finite locally free module on `Y'`. A morphism `j : Z ⟶ Y` represents that
locus when factoring through `j` is equivalent to this descent condition.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- A morphism `g : Y' ⟶ Y` lies in the descent locus of `E` along `f` if
`(g')^* E` is isomorphic to the pullback of some finite locally free
`𝒪_{Y'}`-module. -/
def descendsAlong {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (E : X.Modules) (g : Y' ⟶ Y) : Prop :=
  ∃ (N : Y'.Modules) (_ : N.IsFiniteLocallyFree),
    Nonempty
      ((AlgebraicSpace.Modules.pullback (pullback.snd f g)).obj N ≅
        (AlgebraicSpace.Modules.pullback (pullback.fst f g)).obj E)

/-- Descent along `g` is the existence of a finite locally free module on `Y'`
whose pullback along `f'` recovers the pullback of `E` along `g'`. -/
theorem descendsAlong_iff {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (E : X.Modules) (g : Y' ⟶ Y) :
    descendsAlong f E g ↔
      ∃ (N : Y'.Modules) (_ : N.IsFiniteLocallyFree),
        Nonempty
          ((AlgebraicSpace.Modules.pullback (pullback.snd f g)).obj N ≅
            (AlgebraicSpace.Modules.pullback (pullback.fst f g)).obj E) :=
  Iff.rfl

/-- A morphism `j : Z ⟶ Y` represents the descent locus of `E` along `f` if,
after every base change `g : Y' ⟶ Y`, factoring through `j` is equivalent to
`E` descending along `g`. -/
def RepresentsDescentLocus {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (E : X.Modules) (j : Z ⟶ Y) : Prop :=
  ∀ {Y' : AlgebraicSpace S} (g : Y' ⟶ Y),
    Nonempty (Over.mk g ⟶ Over.mk j) ↔ descendsAlong f E g

/-- The universal property characterizing a morphism that represents the descent
locus of `E` along `f`. -/
theorem representsDescentLocus_iff {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (E : X.Modules) (j : Z ⟶ Y) :
    RepresentsDescentLocus f E j ↔
      ∀ {Y' : AlgebraicSpace S} (g : Y' ⟶ Y),
        Nonempty (Over.mk g ⟶ Over.mk j) ↔ descendsAlong f E g :=
  Iff.rfl

/-- The locus where a finite locally free module descends along a flat proper
finitely presented morphism of algebraic spaces is represented by a finitely
presented immersion, provided the canonical structure-sheaf unit is an
isomorphism after every base change. -/
theorem existsDescentLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [Proper f] [FinitePresentation f]
    (E : X.Modules) [E.IsFiniteLocallyFree]
    (h_unit : ∀ {Y' : AlgebraicSpace S} (g : Y' ⟶ Y),
      IsIso (unitToPushforwardObjUnit (pullback.snd f g))) :
    ∃ (Z : AlgebraicSpace S) (j : Z ⟶ Y) (_ : IsImmersion j)
      (_ : FinitePresentation j), RepresentsDescentLocus f E j :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
