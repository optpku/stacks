/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.AffineOpen.Thickening
public import stacks_project.Chap39.Lemma_39_13_4_Groupoid

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

/- Lemma 40.14.4: A finite, finitely presented groupoid over a quasi-separated object
scheme admits an invariant affine open and an invariant affine thickening of finite
presentation inside it containing any prescribed finite family of points whose orbits
consist of generic points. The thickened subscheme is affine, and both endpoint maps of
the restricted groupoid are finite locally free. -/
@[stacks 0ABC] #check
  (AlgebraicGeometry.GroupoidScheme.exists_invariantAffineOpenThickening_of_finitePresentation :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      [AlgebraicGeometry.IsFinite G.s.left] [AlgebraicGeometry.IsFinite G.t.left]
      [AlgebraicGeometry.Scheme.Hom.FinitePresentation G.s.left]
      [AlgebraicGeometry.Scheme.Hom.FinitePresentation G.t.left]
      [QuasiSeparatedSpace G.U.left]
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
            (h_finitePresentation :
              AlgebraicGeometry.Scheme.Hom.FinitePresentation Z.subschemeι)
            (h_source :
              AlgebraicGeometry.IsFiniteLocallyFree (G.pullback i).s.left),
            AlgebraicGeometry.IsFiniteLocallyFree (G.pullback i).t.left)
