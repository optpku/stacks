/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import stacks_project.Chap87.Definition_87_9_1_Affine

/-!
# Lemma 87.9.5

An fppf sheaf on `(Sch/S)_fppf` is an affine formal algebraic space if and only
if every map from an affine `S`-scheme factors through a representable
thickening from an affine `S`-scheme, and the coequalizer-of-representables
size condition of Remark 87.11.5 holds.
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
  sorry

/-- Lemma 87.9.5: Let `S` be a scheme. Let `X` be a sheaf on `(Sch/S)_fppf`. Then
`X` is an affine formal algebraic space if and only if every morphism `U ⟶ X`
from an affine scheme over `S` factors through a morphism `T ⟶ X` which is
representable and a thickening with `T` affine over `S`, and `X` satisfies the
set-theoretic coequalizer-of-representables condition of Remark 87.11.5. -/
@[stacks 0AIB]
theorem iff_factorsThroughRepresentableAffineThickening
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsAffineFormalAlgebraicSpace X ↔
      factorsThroughRepresentableAffineThickening X ∧ IsCoequalizerOfRepresentables X :=
  sorry

end IsAffineFormalAlgebraicSpace
end AlgebraicGeometry
