module

public import stacks_project.Chap87.Definition_87_38_1_Completion
public import stacks_project.Chap67.Definition_67_13_2_InverseImage

/-!
# Induced maps of completions along inverse-image closed subspaces

A morphism of algebraic spaces induces a morphism of formal completions along a
closed subspace and its inverse image, acting on the fppf-local sheaf of
Definition 87.38.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- If a section of `X'` fppf-locally factors through an infinitesimal
neighbourhood of the inverse image of `i` along `f : X' ⟶ X`, then
postcomposition with `f` fppf-locally factors through an infinitesimal
neighbourhood of `i`. -/
theorem fppfLocallyFactorsThroughNeighbourhood_comp {S : Scheme.{u}}
    {X' X Z : AlgebraicSpace S} (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    {U : (Over S)ᵒᵖ} {x : X'.functorOfPoints.obj U}
    (hx : fppfLocallyFactorsThroughNeighbourhood (inverseImageι f i) x) :
    fppfLocallyFactorsThroughNeighbourhood i (f.app U x) :=
  sorry

namespace completionAlongSubspace

/-- The morphism of completions induced by `f : X' ⟶ X` along the inverse image
closed subspace `Z' = f⁻¹(Z)` given by `inverseImageι f i`. -/
def map {S : Scheme.{u}} {X' X Z : AlgebraicSpace S} (f : X' ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] :
    completionAlongSubspace (inverseImageι f i) ⟶ completionAlongSubspace i where
  app U :=
    ofHom fun x ↦
      ⟨f.app U x.1, fppfLocallyFactorsThroughNeighbourhood_comp f i x.property⟩
  naturality := sorry

/-- The underlying section of `map f i` is the component of `f`. -/
theorem map_app {S : Scheme.{u}} {X' X Z : AlgebraicSpace S} (f : X' ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] (U : (Over S)ᵒᵖ)
    (x : (completionAlongSubspace (inverseImageι f i)).obj U) :
    (ι i).app U ((map f i).app U x) =
      f.app U ((ι (inverseImageι f i)).app U x) :=
  sorry

/-- The square of completions along a closed subspace and its inverse image
commutes. -/
theorem map_comp_ι {S : Scheme.{u}} {X' X Z : AlgebraicSpace S} (f : X' ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] :
    map f i ≫ ι i = ι (inverseImageι f i) ≫ f :=
  sorry

end completionAlongSubspace

end AlgebraicGeometry.AlgebraicSpace
