/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.AffineOpen.Thickening

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

/- Lemma 40.14.5: Given finitely many points of a locally Noetherian groupoid scheme whose
orbits consist of generic points of irreducible components, there is an invariant affine
closed thickening through those points inside an invariant affine open, with finite locally
free restricted source and target maps. -/
@[stacks 0ABD] #check
  (AlgebraicGeometry.GroupoidScheme.exists_invariantAffineOpenThickening :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      [AlgebraicGeometry.IsFinite G.s.left] [AlgebraicGeometry.IsFinite G.t.left]
      [AlgebraicGeometry.IsLocallyNoetherian G.U.left]
      {m : ℕ} (u : Fin m → G.U.left),
      (∀ j, G.t.left '' (G.s.left ⁻¹' {u j}) ⊆ genericPoints G.U.left) →
        ∃ (V : AlgebraicGeometry.Scheme.affineOpens G.U.left)
          (Z : AlgebraicGeometry.Scheme.IdealSheafData (V : AlgebraicGeometry.Scheme)),
          let i : Over.mk
              ((Z.subschemeι ≫ (V : AlgebraicGeometry.Scheme.Opens G.U.left).ι) ≫ G.U.hom) ⟶
                G.U :=
            Over.homMk
              (Z.subschemeι ≫ (V : AlgebraicGeometry.Scheme.Opens G.U.left).ι)
          ∃ (h_V_invariant :
              G.toPreRelation.IsOpenInvariant
                (V : AlgebraicGeometry.Scheme.Opens G.U.left))
            (h_Z_invariant :
              G.toPreRelation.IsInvariant
                (Subobject.mk
                  (Z.subschemeι ≫ (V : AlgebraicGeometry.Scheme.Opens G.U.left).ι)))
            (h_points : ∀ j,
              u j ∈ Set.range
                (Z.subschemeι ≫ (V : AlgebraicGeometry.Scheme.Opens G.U.left).ι))
            (h_Z_affine : AlgebraicGeometry.IsAffine Z.subscheme)
            (h_thickening : AlgebraicGeometry.IsThickening Z.subschemeι)
            (h_source : AlgebraicGeometry.IsFiniteLocallyFree (G.pullback i).s.left),
            AlgebraicGeometry.IsFiniteLocallyFree (G.pullback i).t.left)
