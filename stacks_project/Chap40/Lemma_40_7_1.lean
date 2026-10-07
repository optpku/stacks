module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.FiberComparison
public import stacks_project.Chap39.Lemma_39_13_4_Groupoid

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry

/- Lemma 40.7.1 (1): source fibres of arrows with the same target become isomorphic over a
common residue-field extension. -/
@[stacks 02YF] #check
  (AlgebraicGeometry.GroupoidScheme.existsSourceFiberBaseChangeIso :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S)
      (r r' : G.R.left) (_ : G.t.left r = G.t.left r'),
      ∃ (K : Type u) (_ : Field K)
        (ι : Scheme.residueField G.U.left (G.s.left r) ⟶ CommRingCat.of K)
        (ι' : Scheme.residueField G.U.left (G.s.left r') ⟶ CommRingCat.of K),
        let g := Spec.map ι
        let g' := Spec.map ι'
        Nonempty
          ((Over.pullback g).obj
              (Over.mk (Scheme.Hom.fiberToSpecResidueField G.s.left (G.s.left r))) ≅
            (Over.pullback g').obj
              (Over.mk (Scheme.Hom.fiberToSpecResidueField G.s.left (G.s.left r')))))

/- Lemma 40.7.1 (2): the fibre isomorphism can carry a point over `r` to a point over `r'`. -/
@[stacks 02YF]
#check
  (AlgebraicGeometry.GroupoidScheme.existsSourceFiberBaseChangeIso_mapPoint :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S)
      (r r' : G.R.left) (_ : G.t.left r = G.t.left r'),
      ∃ (K : Type u) (_ : Field K)
        (ι : Scheme.residueField G.U.left (G.s.left r) ⟶ CommRingCat.of K)
        (ι' : Scheme.residueField G.U.left (G.s.left r') ⟶ CommRingCat.of K),
        let g := Spec.map ι
        let g' := Spec.map ι'
        let F := Over.mk (Scheme.Hom.fiberToSpecResidueField G.s.left (G.s.left r))
        let F' := Over.mk (Scheme.Hom.fiberToSpecResidueField G.s.left (G.s.left r'))
        ∃ (e : (Over.pullback g).obj F ≅ (Over.pullback g').obj F')
          (x : ((Over.pullback g).obj F).left),
          pullback.fst F.hom g x = Scheme.Hom.asFiber G.s.left r ∧
            pullback.fst F'.hom g' (e.hom.left x) = Scheme.Hom.asFiber G.s.left r')

/- Lemma 40.7.1 (3): when the source and target maps are flat, their germs at arrows with a
common target are flat locally on the base isomorphic. -/
@[stacks 02YF]
#check
  (AlgebraicGeometry.GroupoidScheme.sourceGermsFlatLocallyIsomorphic :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S) [Flat G.s.left] [Flat G.t.left]
      (r r' : G.R.left) (_ : G.t.left r = G.t.left r'),
      Scheme.Germ.Hom.IsLocallyOnBaseIsomorphic
        Scheme.Germ.MorphismProperty.flat
        (Scheme.Germ.Hom.ofGlobal G.s.left rfl :
          Scheme.Germ.of G.R.left r ⟶ Scheme.Germ.of G.U.left (G.s.left r))
        (Scheme.Germ.Hom.ofGlobal G.s.left rfl :
          Scheme.Germ.of G.R.left r' ⟶ Scheme.Germ.of G.U.left (G.s.left r')))

/- Lemma 40.7.1 (4): for any non-Zariski standard topology, source-map germs at arrows with a
common target are locally on the base isomorphic when both structure maps have the topology's
defining property. -/
@[stacks 02YF]
#check
  (AlgebraicGeometry.GroupoidScheme.sourceGermsLocallyIsomorphic :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S)
      (r r' : G.R.left) (_ : G.t.left r = G.t.left r')
      (τ : StandardTopology) (_ : τ ≠ .zariski)
      (_ : StandardTopology.Small.morphismProperty τ G.s.left)
      (_ : StandardTopology.Small.morphismProperty τ G.t.left),
      Scheme.Germ.Hom.IsLocallyOnBaseIsomorphic
        (Scheme.Germ.MorphismProperty.representedBy
          (StandardTopology.Small.morphismProperty τ))
        (Scheme.Germ.Hom.ofGlobal G.s.left rfl :
          Scheme.Germ.of G.R.left r ⟶ Scheme.Germ.of G.U.left (G.s.left r))
        (Scheme.Germ.Hom.ofGlobal G.s.left rfl :
          Scheme.Germ.of G.R.left r' ⟶ Scheme.Germ.of G.U.left (G.s.left r')))

end AlgebraicGeometry
