module

public import stacks_project.Chap76.Lemma_76_20_3_InfinitesimalNeighbourhood
import StacksCheckRecall

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.InfinitesimalNeighbourhood

/- Lemma 76.20.3 (1): if every base change of a locally finite-type morphism of
algebraic spaces to an infinitesimal neighbourhood of a closed subspace of a
locally Noetherian target is smooth, then the morphism is smooth at every point
lying above that closed subspace. -/
@[stacks 0APQ] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.InfinitesimalNeighbourhood.smoothAt_of_smooth_pullbacks :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y)
      [LocallyOfFiniteType f] [IsLocallyNoetherian Y]
      (i : Z ⟶ Y) [IsClosedImmersion i]
      [∀ n : ℕ, Smooth (pullback.snd f (toAmbient i n))]
      (x : Points X) (_ : Points.map f x ∈ Set.range (Points.map i)),
      SmoothAt f x)

/- Lemma 76.20.3 (2): if every base change of a locally finite-type morphism of
algebraic spaces to an infinitesimal neighbourhood of a closed subspace of a
locally Noetherian target is étale, then the morphism is étale at every point
lying above that closed subspace. -/
@[stacks 0APQ] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.InfinitesimalNeighbourhood.etaleAt_of_etale_pullbacks :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y)
      [LocallyOfFiniteType f] [IsLocallyNoetherian Y]
      (i : Z ⟶ Y) [IsClosedImmersion i]
      [∀ n : ℕ, Etale (pullback.snd f (toAmbient i n))]
      (x : Points X) (_ : Points.map f x ∈ Set.range (Points.map i)),
      EtaleAt f x)

end AlgebraicGeometry.AlgebraicSpace.Hom.InfinitesimalNeighbourhood
