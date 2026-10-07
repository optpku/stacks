module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree.ChernClass

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- Lemma 42.41.3: The curve degree of a constant-rank finite locally free module on a
proper scheme over a field of dimension at most one is the degree of its first Chern class
capped with the degree-one fundamental class. -/
@[stacks 0AZ3] #check
  (AlgebraicGeometry.Scheme.Modules.curveDegree_eq_chowDegree_firstChernClassCap :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.IsProper X.hom],
    (hdim : topologicalKrullDim X.left ≤ 1)
    → ∀ (E : X.left.Modules) (n : ℕ)
      [AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank n E],
      AlgebraicGeometry.Scheme.Modules.curveDegree X.hom hdim E n =
        AlgebraicGeometry.ChowGroup.degree X
        ((AlgebraicGeometry.ChernClass.chernClass
          (fun _ : AlgebraicGeometry.Spec (CommRingCat.of k) ↦ 0) X.hom E 1).cap
          (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom))
          IsPullback.of_id_snd 1
          (@AlgebraicGeometry.chowClass X.left
            (AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian X.hom)
            (X.hom.relativeDimensionFunction
              (fun _ : AlgebraicGeometry.Spec (CommRingCat.of k) ↦ 0))
            inferInstance 1
            (@AlgebraicGeometry.CycleGroup.fundamental X.left
              (AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian X.hom)
              (X.hom.relativeDimensionFunction
                (fun _ : AlgebraicGeometry.Spec (CommRingCat.of k) ↦ 0)) 1))))
