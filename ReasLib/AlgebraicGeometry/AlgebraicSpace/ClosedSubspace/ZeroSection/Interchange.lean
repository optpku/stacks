/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.ZeroSection.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InvertiblePullback

/-! # Interchange of iterated zero schemes -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DoubleZero

/-- The iterated zero scheme obtained by restricting one section to the zero
scheme of another section. -/
noncomputable abbrev iterate {S : Scheme.{u}} {X : AlgebraicSpace S}
    (L L' : X.Modules) [isInvertibleObject L] [isInvertibleObject L']
    (s : L.sections) (s' : L'.sections) :
    ClosedSubspace (zeroScheme L s).X :=
  zeroScheme ((Modules.pullback (zeroSchemeι L s)).obj L')
    (Modules.sectionsPullback (zeroSchemeι L s) L' s')

/-- The canonical isomorphism exchanging the order of two zero-scheme
constructions. -/
noncomputable def swapIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    (L L' : X.Modules) [isInvertibleObject L] [isInvertibleObject L']
    (s : L.sections) (s' : L'.sections) :
    (iterate L' L s' s).X ≅ (iterate L L' s s').X := by
  let hA := zeroSchemePullbackSquare (zeroSchemeι L' s') L s
  let hB := zeroSchemePullbackSquare (zeroSchemeι L s) L' s'
  exact hA.isoIsPullback _ _ hB.flip

/-- The interchange isomorphism followed by the immersion into `Z(s)` equals
the canonical pullback projection to `Z(s)`. -/
theorem swapIso_hom_fst {S : Scheme.{u}} {X : AlgebraicSpace S}
    (L L' : X.Modules) [isInvertibleObject L] [isInvertibleObject L']
    (s : L.sections) (s' : L'.sections) :
    (swapIso L L' s s').hom ≫ (iterate L L' s s').ι =
      zeroSchemePullbackMap (zeroSchemeι L' s') L s := by
  let hA := zeroSchemePullbackSquare (zeroSchemeι L' s') L s
  let hB := zeroSchemePullbackSquare (zeroSchemeι L s) L' s'
  exact hA.isoIsPullback_hom_snd _ _ hB.flip

/-- The interchange isomorphism followed by the canonical map to `Z(s')` equals
the immersion of the other iterated zero scheme. -/
theorem swapIso_hom_snd {S : Scheme.{u}} {X : AlgebraicSpace S}
    (L L' : X.Modules) [isInvertibleObject L] [isInvertibleObject L']
    (s : L.sections) (s' : L'.sections) :
    (swapIso L L' s s').hom ≫
        zeroSchemePullbackMap (zeroSchemeι L s) L' s' =
      (iterate L' L s' s).ι := by
  let hA := zeroSchemePullbackSquare (zeroSchemeι L' s') L s
  let hB := zeroSchemePullbackSquare (zeroSchemeι L s) L' s'
  exact hA.isoIsPullback_hom_fst _ _ hB.flip

/-- The interchange isomorphism is compatible with the structure morphism to a
common algebraic space. -/
theorem swapIso_hom_comp_structure {S : Scheme.{u}}
    {B X : AlgebraicSpace S} (f : X ⟶ B)
    (L L' : X.Modules) [isInvertibleObject L] [isInvertibleObject L']
    (s : L.sections) (s' : L'.sections) :
    (swapIso L L' s s').hom ≫
        ((iterate L L' s s').ι ≫ zeroSchemeι L s ≫ f) =
      (iterate L' L s' s).ι ≫ zeroSchemeι L' s' ≫ f := by
  rw [← Category.assoc, swapIso_hom_fst, ← Category.assoc,
    zeroSchemePullbackMap_comp, Category.assoc]

end AlgebraicGeometry.AlgebraicSpace.DoubleZero
