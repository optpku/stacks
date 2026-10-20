/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Cover.Ph.BaseChange
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 34.8.2: a standard ph covering remains a standard ph covering after base change
along a morphism of affine schemes. -/
@[stacks 0DBE] #check
  (AlgebraicGeometry.StandardPhCovering.pullbackFamily :
    ∀ {T T' : AlgebraicGeometry.Scheme.{u}}
      [AlgebraicGeometry.IsAffine T] [AlgebraicGeometry.IsAffine T']
      (Φ : AlgebraicGeometry.StandardPhCovering T) (g : T' ⟶ T) (j : Fin Φ.m),
      pullback.snd (Φ.map j) g =
        (Φ.pullbackObjIso g j).hom ≫ (Φ.pullback g).map j)
