/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.GroupoidScheme
public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.LocalIsomorphism
public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.RepresentedBy
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Small

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- Source fibres of arrows with the same target become isomorphic after base change to a
common extension of their source residue fields. -/
theorem existsSourceFiberBaseChangeIso {S : Scheme.{u}} (G : GroupoidScheme S)
    (r r' : G.R.left) (h_target : G.t.left r = G.t.left r') :
    ∃ (K : Type u) (_ : Field K)
      (ι : Scheme.residueField G.U.left (G.s.left r) ⟶ CommRingCat.of K)
      (ι' : Scheme.residueField G.U.left (G.s.left r') ⟶ CommRingCat.of K),
      let g := Spec.map ι
      let g' := Spec.map ι'
      Nonempty
        ((Over.pullback g).obj
            (Over.mk (Scheme.Hom.fiberToSpecResidueField G.s.left (G.s.left r))) ≅
          (Over.pullback g').obj
            (Over.mk (Scheme.Hom.fiberToSpecResidueField G.s.left (G.s.left r')))) := sorry

/-- The common-field source-fibre isomorphism can carry a point above the first arrow to a
point above the second arrow. -/
theorem existsSourceFiberBaseChangeIso_mapPoint {S : Scheme.{u}} (G : GroupoidScheme S)
    (r r' : G.R.left) (h_target : G.t.left r = G.t.left r') :
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
          pullback.fst F'.hom g' (e.hom.left x) = Scheme.Hom.asFiber G.s.left r' := sorry

/-- When both structure maps are flat, the source-map germs at arrows with a common target
are flat locally on the base isomorphic. -/
theorem sourceGermsFlatLocallyIsomorphic {S : Scheme.{u}} (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left] (r r' : G.R.left)
    (h_target : G.t.left r = G.t.left r') :
    Scheme.Germ.Hom.IsLocallyOnBaseIsomorphic
      Scheme.Germ.MorphismProperty.flat
      (Scheme.Germ.Hom.ofGlobal G.s.left rfl :
        Scheme.Germ.of G.R.left r ⟶ Scheme.Germ.of G.U.left (G.s.left r))
      (Scheme.Germ.Hom.ofGlobal G.s.left rfl :
        Scheme.Germ.of G.R.left r' ⟶ Scheme.Germ.of G.U.left (G.s.left r')) := sorry

/-- For a non-Zariski standard topology, the source-map germs at arrows with a common target
are locally on the base isomorphic when both structure maps have the topology's defining
morphism property. -/
theorem sourceGermsLocallyIsomorphic {S : Scheme.{u}} (G : GroupoidScheme S)
    (r r' : G.R.left) (h_target : G.t.left r = G.t.left r')
    (τ : StandardTopology) (hτ : τ ≠ .zariski)
    (hs : StandardTopology.Small.morphismProperty τ G.s.left)
    (ht : StandardTopology.Small.morphismProperty τ G.t.left) :
    Scheme.Germ.Hom.IsLocallyOnBaseIsomorphic
      (Scheme.Germ.MorphismProperty.representedBy
        (StandardTopology.Small.morphismProperty τ))
      (Scheme.Germ.Hom.ofGlobal G.s.left rfl :
        Scheme.Germ.of G.R.left r ⟶ Scheme.Germ.of G.U.left (G.s.left r))
      (Scheme.Germ.Hom.ofGlobal G.s.left rfl :
        Scheme.Germ.of G.R.left r' ⟶ Scheme.Germ.of G.U.left (G.s.left r')) := sorry

end AlgebraicGeometry.GroupoidScheme
