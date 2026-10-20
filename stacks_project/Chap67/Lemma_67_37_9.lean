module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth.SourceLocus
import StacksCheckRecall

/-!
# Largest open subspace on which a morphism of algebraic spaces is smooth

There is a largest open subspace of the source on which a morphism of algebraic
spaces is smooth, and formation of this open commutes with cartesian base change
along morphisms that are flat and locally of finite presentation, and along
flat morphisms when the original morphism is locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.37.9: Every morphism of algebraic spaces has a largest open source
subspace on which it is smooth. Its formation commutes with flat base change
locally of finite presentation, and with flat base change when the original
morphism is locally of finite presentation. -/
@[stacks 0DZI] #check (AlgebraicGeometry.AlgebraicSpace.Smooth.sourceLocus_isLargest :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    Smooth ((Smooth.sourceLocus f).ι ≫ f) ∧
      ∀ {U : AlgebraicSpace S} (i : U ⟶ X) [IsOpenImmersion i],
        Smooth (i ≫ f) →
          Set.range (Points.map i) ⊆
            Set.range (Points.map (Smooth.sourceLocus f).ι))

#check (AlgebraicGeometry.AlgebraicSpace.Smooth.sourceLocus_eq_preimage_of_flat_locallyOfFinitePresentation :
  ∀ {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hcart : IsPullback g' f' f g) [Flat g] [LocallyOfFinitePresentation g],
    Set.range (Points.map (Smooth.sourceLocus f').ι) =
      (Points.map g') ⁻¹' Set.range (Points.map (Smooth.sourceLocus f).ι))

#check (AlgebraicGeometry.AlgebraicSpace.Smooth.sourceLocus_eq_preimage_of_flat_base :
  ∀ {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hcart : IsPullback g' f' f g) [LocallyOfFinitePresentation f] [Flat g],
    Set.range (Points.map (Smooth.sourceLocus f').ι) =
      (Points.map g') ⁻¹' Set.range (Points.map (Smooth.sourceLocus f).ι))

end AlgebraicGeometry.AlgebraicSpace
