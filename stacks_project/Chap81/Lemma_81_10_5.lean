module

public import stacks_project.Chap67.Definition_67_13_2_InverseImage
public import stacks_project.Chap67.Lemma_67_13_5_Complement
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap75.Definition_75_3_2_SupportedOn
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap81.Lemma_81_10_5_Adjunction

/-!
# Lemma 81.10.5

If `f⁻¹Z ⟶ Z` is an isomorphism and `f` is flat at every point of `|f⁻¹Z|`,
then for a quasi-coherent complex supported on `|f⁻¹Z|` the derived
pullback-pushforward counit is an isomorphism.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- Lemma 81.10.5: Let `S` be a scheme. Let `f : Y ⟶ X` be a morphism of algebraic
spaces over `S`. Let `i : Z ⟶ X` be a closed immersion. Assume `inverseImageTo f i`
is an isomorphism and that `f` is flat at every point of
`pointsImage (inverseImageι f i)`. For any `Q` in `DerivedQCoh Y` supported on
`|f⁻¹Z|`, the canonical counit
`(modulePullbackDerivedPushforwardAdjunction f).counit.app Q.obj` is an isomorphism
in `D(𝒪_Y)`. -/
@[stacks 0AEU]
theorem derivedPullback_pushforward_counit_isIso {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i]
    [IsIso (inverseImageTo f i)]
    (hf : ∀ x : Points Y, x ∈ pointsImage (inverseImageι f i) → FlatAt f x)
    (Q : DerivedQCoh Y)
    (hQ : ModuleDerived.IsSupportedOn Q.obj (pointsImage (inverseImageι f i))) :
    IsIso ((modulePullbackDerivedPushforwardAdjunction f).counit.app Q.obj) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
