module

public import stacks_project.Chap63.Lemma_63_4_7_Cech

/-!
# Exact Čech complex of locally quasi-finite lower shrieks

Lemma 63.4.7: for a locally quasi-finite morphism and an open covering of the
source, the functorial augmented Čech chain complex of compact-support direct
images is acyclic.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open HomologicalComplex
open TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Lemma 63.4.7: Let `f : X ⟶ Y` be a locally quasi-finite morphism of
schemes, and let `𝒰 : ι → X.Opens` be an open covering of `X`. Then for
`F` in `Ab(X_étale)` the functorial augmented Čech chain complex
`lowerShriekCechAugmentedComplex f 𝒰 F`, with coproduct terms
`lowerShriekCechTerm f 𝒰 F n` of summands `f_{∩σ,!}(F|_{∩σ})` and
augmentation `f_! F`, is acyclic. -/
@[stacks 0F5H]
theorem lowerShriekCechAugmentedComplex_acyclic {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyQuasiFinite f]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasCoproducts.{u} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
    {ι : Type u} (𝒰 : ι → X.Opens) (h𝒰 : IsOpenCover 𝒰)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriekCechAugmentedComplex f 𝒰 F).Acyclic :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
