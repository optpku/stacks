module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Full

/-!
# Characterization of affine formal algebraic spaces

Affine formal algebraic spaces on the full big fppf site are characterized by
factorization through affine representable thickenings and the fixed-site
presentation condition.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry
namespace IsAffineFormalAlgebraicSpace

/-- Every morphism from an affine scheme over `S` into the fppf sheaf `X` factors
through a morphism from an affine scheme over `S` which is relatively
representable and a relative thickening. -/
def factorsThroughRepresentableAffineThickening
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop :=
  ∀ (U : 𝒮.bigAffineSite S)
    (f : (𝒮.bigTopology S).sheafifiedRepresentable ((𝒮.bigAffineInclusion S).obj U) ⟶ X),
    ∃ (T : 𝒮.bigAffineSite S) (φ : U ⟶ T)
      (t : (𝒮.bigTopology S).sheafifiedRepresentable ((𝒮.bigAffineInclusion S).obj T) ⟶ X),
      (𝒮.bigTopology S).sheafifiedRepresentableMap ((𝒮.bigAffineInclusion S).map φ) ≫ t = f ∧
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable t ∧
        (MorphismProperty.inverseImage (@IsThickening) (𝒮.bigToScheme S)).relative
          (𝒮.bigTopology S).sheafifiedRepresentableFunctor t

/-- The factorization condition unpacks as: for every affine `U` over `S` and
every morphism `f` from the sheafified representable of `U` into `X`, there
exist an affine `T` over `S`, a site morphism `φ : U ⟶ T`, and a morphism `t`
from the sheafified representable of `T` into `X` with
`sheafifiedRepresentableMap (bigAffineInclusion.map φ) ≫ t = f`, such that `t`
is relatively representable and a relative thickening. -/
theorem factorsThroughRepresentableAffineThickening_iff
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    factorsThroughRepresentableAffineThickening X ↔
      ∀ (U : 𝒮.bigAffineSite S)
        (f : (𝒮.bigTopology S).sheafifiedRepresentable ((𝒮.bigAffineInclusion S).obj U) ⟶ X),
        ∃ (T : 𝒮.bigAffineSite S) (φ : U ⟶ T)
          (t : (𝒮.bigTopology S).sheafifiedRepresentable ((𝒮.bigAffineInclusion S).obj T) ⟶ X),
          (𝒮.bigTopology S).sheafifiedRepresentableMap ((𝒮.bigAffineInclusion S).map φ) ≫ t = f ∧
            (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable t ∧
            (MorphismProperty.inverseImage (@IsThickening) (𝒮.bigToScheme S)).relative
              (𝒮.bigTopology S).sheafifiedRepresentableFunctor t :=
  Iff.rfl

/-- A sheaf on the full big fppf site of a scheme is an affine formal algebraic
space if and only if every morphism from an affine scheme factors through an
affine representable thickening and the sheaf satisfies the fixed-site
coequalizer-of-representables condition. -/
theorem iff_factorsThroughRepresentableAffineThickening
    {S : Scheme.{u}}
    [HasWeakSheafify (ChosenBigFppfSite.full.bigTopology S) (Type (u + 1))]
    [HasPullbacks (Sheaf (ChosenBigFppfSite.full.bigTopology S) (Type (u + 1)))]
    (X : Sheaf (ChosenBigFppfSite.full.bigTopology S) (Type (u + 1))) :
    IsAffineFormalAlgebraicSpace X ↔
      factorsThroughRepresentableAffineThickening X ∧ IsCoequalizerOfRepresentables X :=
  sorry

end IsAffineFormalAlgebraicSpace
end AlgebraicGeometry
