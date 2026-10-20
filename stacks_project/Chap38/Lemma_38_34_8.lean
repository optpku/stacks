/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.H.Stability
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

/- Lemma 38.34.8 (1): a family of locally finitely presented morphisms is an h
covering exactly when it admits a refining h covering family. -/
@[stacks 0ETX]
#check (AlgebraicGeometry.Scheme.hCovering_iff_exists_refinement :
  ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v} (family : ι → Over T),
    (∀ i, AlgebraicGeometry.LocallyOfFinitePresentation (family i).hom) →
      (AlgebraicGeometry.Scheme.HCovering family ↔
        ∃ (κ : Type v) (refining : κ → Over T),
          AlgebraicGeometry.Scheme.HCovering refining ∧
            SemiRepresentableFamily.Over.Refines
              (SemiRepresentableFamily.Over.ofArrows
                (fun k ↦ (refining k).left) (fun k ↦ (refining k).hom))
              (SemiRepresentableFamily.Over.ofArrows
                (fun i ↦ (family i).left) (fun i ↦ (family i).hom))))

/- Lemma 38.34.8 (2): a family of locally finitely presented morphisms is an h
covering exactly when its coproduct map, viewed as a singleton family, is an h
covering. -/
@[stacks 0ETX]
#check (AlgebraicGeometry.Scheme.hCovering_iff_coproductSingleton :
  ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type u} (family : ι → Over T),
    (∀ i, AlgebraicGeometry.LocallyOfFinitePresentation (family i).hom) →
      (AlgebraicGeometry.Scheme.HCovering family ↔
        AlgebraicGeometry.Scheme.HCovering (fun p ↦
          (FormalCoproduct.Over.coproductSingleton
            (FormalCoproduct.ofArrows
              (fun i ↦ (family i).left) (fun i ↦ (family i).hom))).obj p)))
