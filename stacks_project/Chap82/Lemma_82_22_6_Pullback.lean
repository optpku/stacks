/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Definition_67_33_2_RelativeDimension
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap82.Remark_82_22_3_Pullback

/-!
# Flatness and relative dimension of zero-scheme pullback maps

The canonical map `g : D' ⟶ D` of Remark 82.22.3 is flat of the same relative
dimension as `f : X' ⟶ X`, and it commutes with structure morphisms to a
common base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The canonical map from the zero scheme of a pulled-back section is flat
whenever the original morphism is flat. -/
instance instFlat_zeroSchemePullbackMap {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} (f : X' ⟶ X) [Flat f] (L : X.Modules)
    [isInvertibleObject L] (s : L.sections)
    [isInvertibleObject ((Modules.pullback f).obj L)] :
    Flat (zeroSchemePullbackMap f L s) :=
  sorry

/-- The canonical map from the zero scheme of a pulled-back section has the
relative dimension of the original morphism. -/
instance instRelativeDimension_zeroSchemePullbackMap {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} (f : X' ⟶ X) (r : ℕ) [RelativeDimension f r]
    (L : X.Modules) [isInvertibleObject L] (s : L.sections)
    [isInvertibleObject ((Modules.pullback f).obj L)] :
    RelativeDimension (zeroSchemePullbackMap f L s) r :=
  sorry

/-- The zero-scheme pullback map commutes with structure morphisms to a common
base. -/
theorem zeroSchemePullbackMap_comp_structure {S : Scheme.{u}}
    {B X X' : AlgebraicSpace S} (pX : X ⟶ B) (pX' : X' ⟶ B) (f : X' ⟶ X)
    (hf : f ≫ pX = pX') (L : X.Modules) [isInvertibleObject L]
    (s : L.sections) [isInvertibleObject ((Modules.pullback f).obj L)] :
    zeroSchemePullbackMap f L s ≫ (zeroSchemeι L s ≫ pX) =
      zeroSchemeι ((Modules.pullback f).obj L) (Modules.sectionsPullback f L s) ≫
        pX' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
