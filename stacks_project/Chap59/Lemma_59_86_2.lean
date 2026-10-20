/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.HorizontalComposition
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 59.86.2 (1): in a tower of cartesian squares of schemes, the derived
   base-change horizontal-composition criterion is represented by the canonical
   étale base-change declaration. -/
@[stacks 0EZS] #check (AlgebraicGeometry.Scheme.Etale.BaseChange.etaleDerivedBaseChange_comp_isIso :
  ∀ {W Z X Y S T : Scheme.{u}}
    (i : W ⟶ X) (j : Z ⟶ W) (k : Z ⟶ Y) (f : X ⟶ S)
    (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (h₁ : IsPullback j k i h) (h₀ : IsPullback h e f g)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    [IsIso (AlgebraicGeometry.Scheme.Etale.BaseChange.derivedMap f h e g h₀ K)]
    [IsIso (AlgebraicGeometry.Scheme.Etale.BaseChange.derivedMap i j k h h₁
      ((AlgebraicGeometry.Scheme.Etale.Derived.inverseImage e).obj K))],
    IsIso (AlgebraicGeometry.Scheme.Etale.BaseChange.derivedMap (i ≫ f) j (k ≫ e) g
      (h₁.paste_vert h₀) K))

/- Lemma 59.86.2 (2): for an abelian sheaf on the small étale site, the
   degreewise higher-direct-image horizontal-composition criterion is
   represented by the canonical étale base-change declaration. -/
@[stacks 0EZS] #check (AlgebraicGeometry.Scheme.Etale.BaseChange.etaleHigherDirectImageBaseChange_comp_isIso :
  ∀ {W Z X Y S T : Scheme.{u}}
    (i : W ⟶ X) (j : Z ⟶ W) (k : Z ⟶ Y) (f : X ⟶ S)
    (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (h₁ : IsPullback j k i h) (h₀ : IsPullback h e f g)
    (q : ℕ) (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    [IsIso (AlgebraicGeometry.Scheme.Etale.BaseChange.higherMap f h e g h₀ q F)]
    [IsIso (AlgebraicGeometry.Scheme.Etale.BaseChange.higherMap i j k h h₁ q
      ((AlgebraicGeometry.Scheme.Etale.Abelian.inverseImage e).obj F))],
    IsIso (AlgebraicGeometry.Scheme.Etale.BaseChange.higherMap (i ≫ f) j (k ≫ e) g
      (h₁.paste_vert h₀) q F))

end

end
