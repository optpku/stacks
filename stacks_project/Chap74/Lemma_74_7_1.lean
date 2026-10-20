/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fpqc.Opens
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits TopologicalSpace

universe u v

/- Lemma 74.7.1: compatible open subspaces on an fpqc covering of algebraic
spaces descend to an open subspace of the target, unique up to unique lift. -/
@[stacks 04P1] #check (AlgebraicGeometry.AlgebraicSpace.FpqcCovering.existsUnique_openSubspace :
  ∀ {S : Scheme.{u}} {T : AlgebraicSpace S} {ι : Type v}
    {family : ι → Over T} (hfamily : FpqcCovering family)
    (W : (i : ι) → OpenSubspace (family i).left)
    (hcompat : ∀ i j : ι,
      ((W i).inverseImage (pullback.fst (family i).hom (family j).hom)).pointsSet =
        ((W j).inverseImage (pullback.snd (family i).hom (family j).hom)).pointsSet),
    ∃ U : OpenSubspace T,
      (∀ i : ι,
          (W i).pointsSet = (U.inverseImage (family i).hom).pointsSet) ∧
        ∀ U' : OpenSubspace T,
          (∀ i : ι,
              (W i).pointsSet = (U'.inverseImage (family i).hom).pointsSet) →
            ∃! φ : U'.X ⟶ U.X, φ ≫ U.ι = U'.ι)

#check (AlgebraicGeometry.AlgebraicSpace.FpqcCovering.existsUnique_open :
  ∀ {S : Scheme.{u}} {T : AlgebraicSpace S} {ι : Type v}
    {family : ι → Over T} (hfamily : FpqcCovering family)
    (W : (i : ι) → OpenSubspace (family i).left)
    (hcompat : ∀ i j : ι,
      ((W i).inverseImage (pullback.fst (family i).hom (family j).hom)).pointsSet =
        ((W j).inverseImage (pullback.snd (family i).hom (family j).hom)).pointsSet),
    ∃! V : Opens (Points T),
      ∀ i : ι,
        (W i).pointsSet =
          Points.map (family i).hom ⁻¹' V.carrier)
