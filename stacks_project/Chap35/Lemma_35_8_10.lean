module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Properties
import StacksCheckRecall

universe u

/- Lemma 35.8.10 (1): on every standard big site, the associated module
preserves and reflects each listed property other than local freeness and
coherence. -/
@[stacks 05VG] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.Property.big_iff :
    ∀ (P : AlgebraicGeometry.Scheme.AssociatedModule.Property)
      (τ : AlgebraicGeometry.StandardTopology) (S : AlgebraicGeometry.Scheme.{u})
      (F : AlgebraicGeometry.Scheme.QCoh S),
      P.scheme F ↔ P.big τ S F)

/- Lemma 35.8.10 (2): on every standard small site, the associated module
preserves and reflects each listed property other than local freeness and
coherence. -/
@[stacks 05VG] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.Property.small_iff :
    ∀ (P : AlgebraicGeometry.Scheme.AssociatedModule.Property)
      (τ : AlgebraicGeometry.StandardTopology) (S : AlgebraicGeometry.Scheme.{u})
      (F : AlgebraicGeometry.Scheme.QCoh S),
      P.scheme F ↔ P.small τ S F)

/- Lemma 35.8.10 (3): on a locally Noetherian scheme, the associated module
on the small Zariski or étale site preserves and reflects coherence. -/
@[stacks 05VG] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.coherent_small_iff :
    ∀ (σ : AlgebraicGeometry.SmallStandardTopology)
      (S : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian S]
      (F : AlgebraicGeometry.Scheme.QCoh S),
      F.obj.IsCoherent ↔
        ((AlgebraicGeometry.Scheme.AssociatedModule.StandardSmall.functor
          σ.toStandard S).obj F).obj.IsCoherent)
