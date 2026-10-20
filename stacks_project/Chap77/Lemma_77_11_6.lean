module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flattening.InDimensions.Etale
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry
namespace AlgebraicSpace.Flattening

/- Lemma 77.11.6 (1): the flat-in-dimensions subfunctor for a module is contained in
the corresponding subfunctor after pulling the module back along an étale morphism. -/
@[stacks 0CX0] #check
  (AlgebraicGeometry.AlgebraicSpace.Flattening.flatInDimensionsSubfunctor.le_of_etale :
    ∀ {S : Scheme.{u}} {X X' Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (n : ℕ)
      (h : X' ⟶ X) [Etale h],
      flatInDimensionsSubfunctor f ℱ n ≤
        flatInDimensionsSubfunctor (h ≫ f) ((Modules.pullback h).obj ℱ) n)

/- Lemma 77.11.6 (2): if the image of an étale morphism contains the relative assassin,
then pulling back the module along it does not change the flat-in-dimensions subfunctor. -/
@[stacks 0CX0] #check
  (AlgebraicGeometry.AlgebraicSpace.Flattening.flatInDimensionsSubfunctor.eq_of_relativeAssassin_subset_range :
    ∀ {S : Scheme.{u}} {X X' Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (n : ℕ)
      (h : X' ⟶ X) [Etale h]
      (h_ass : Set.Subset (Modules.RelativeWeakAss.existsField f ℱ)
        (Set.range (Points.map h))),
      flatInDimensionsSubfunctor f ℱ n =
        flatInDimensionsSubfunctor (h ≫ f) ((Modules.pullback h).obj ℱ) n)

end AlgebraicSpace.Flattening
end AlgebraicGeometry
