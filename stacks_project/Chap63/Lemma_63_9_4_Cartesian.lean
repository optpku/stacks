/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Compactification.BaseChange
public import stacks_project.Chap63.Lemma_63_8_5_Comparison
public import stacks_project.Chap63.Lemma_63_9_2_Comparison

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Compactification

universe u

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
  (f' : X' ⟶ Y') (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g)
  (P : Of Y (Over.mk f))

/- Lemma 63.9.4: the compactification obtained by base change has the new interior. -/
#check (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.compactificationPullback
  f g f' g' h_cart P : Of Y' (Over.mk f'))

end
