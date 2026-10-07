module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import stacks_project.Chap66.Lemma_66_18_12_Pushforward

/-!
# Étale cohomology with support in a closed subspace

Module-facing cohomology with support `H^q_Z(X, F)` is the right-derived functor of
sections-with-support followed by degree-zero sheaf cohomology on `Z`, evaluated on
the underlying abelian sheaf of an `𝒪_X`-module, in the coefficient universe of
`AlgebraicSpace.cohomology`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `cohomologyWithSupport`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Cohomology with support in a closed immersion `i : Z ⟶ X`, as the right-derived functor of
`sectionsWithSupport ⋙ Sheaf.functorH Z 0` on the underlying abelian sheaf of an `𝒪_X`-module. -/
noncomputable def cohomologyWithSupport {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i]
    [∀ P : (smallEtaleSite Z)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallEtaleInclusion Z).op.HasPointwiseRightKanExtension P]
    (sectionsWithSupport :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u})
    (adj : sheafPushforward AddCommGrpCat.{u} i ⊣ sectionsWithSupport)
    (F : X.Modules) (q : ℕ)
    [HasSheafify (smallEtaleTopology Z) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u})]
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [sectionsWithSupport.Additive] :
    AddCommGrpCat.{u} :=
  ((sectionsWithSupport ⋙ Sheaf.functorH (smallEtaleTopology Z) 0).rightDerived q).obj
    ((SheafOfModules.toSheaf (structureSheaf X)).obj F)

/-- `cohomologyWithSupport` is the right-derived evaluation of
`sectionsWithSupport ⋙ Sheaf.functorH Z 0` on `toSheaf F`. -/
theorem cohomologyWithSupport_eq {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i]
    [∀ P : (smallEtaleSite Z)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallEtaleInclusion Z).op.HasPointwiseRightKanExtension P]
    (sectionsWithSupport :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u})
    (adj : sheafPushforward AddCommGrpCat.{u} i ⊣ sectionsWithSupport)
    (F : X.Modules) (q : ℕ)
    [HasSheafify (smallEtaleTopology Z) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u})]
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [sectionsWithSupport.Additive] :
    cohomologyWithSupport i sectionsWithSupport adj F q =
      ((sectionsWithSupport ⋙ Sheaf.functorH (smallEtaleTopology Z) 0).rightDerived q).obj
        ((SheafOfModules.toSheaf (structureSheaf X)).obj F) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
