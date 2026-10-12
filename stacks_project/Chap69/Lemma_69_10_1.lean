/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Definition_66_9_2_Dimension
public import stacks_project.Chap66.Definition_66_29_1_QCoh
public import stacks_project.Chap67.Lemma_67_13_5_Complement
public import stacks_project.Chap69.Lemma_69_10_1_Restriction
public import stacks_project.Chap69.Lemma_69_10_1_CohomologyWithSupport

/-!
# Lemma 69.10.1

Vanishing of étale cohomology of quasi-coherent modules on a quasi-compact
quasi-separated algebraic space above the dimension, together with surjectivity
of restriction in the top degree and vanishing of cohomology with support.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `cohomologyWithSupport`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 69.10.1 (1): étale cohomology of a quasi-coherent module on a quasi-compact
quasi-separated algebraic space vanishes in degrees strictly larger than `dim X`. -/
@[stacks 0A4R]
theorem cohomology_isZero_of_dimension_le
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (d : ℕ) (hdim : dimension X ≤ d) (F : X.Modules) [F.IsQuasicoherent]
    {q : ℕ} (hq : d < q)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})] :
    IsZero (cohomology X F q) :=
  sorry

/-- Lemma 69.10.1 (2): in the top degree allowed by `dim X`, restriction of étale
cohomology of a quasi-coherent module to a quasi-compact open subspace is surjective. -/
@[stacks 0A4R]
theorem cohomologyRestrict_surjective_of_dimension_le
    {S : Scheme.{u}} {X U : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (d : ℕ) (hdim : dimension X ≤ d)
    (ι : U ⟶ X) [IsOpenImmersion ι] [IsQuasiCompact U]
    (F : X.Modules) [F.IsQuasicoherent]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasSheafify (smallEtaleTopology U) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf (smallEtaleTopology U) AddCommGrpCat.{u})]
    [(etaleRestrictionSheaf ι AddCommGrpCat.{u}).Additive]
    [PreservesFiniteLimits (etaleRestrictionSheaf ι AddCommGrpCat.{u})]
    [PreservesFiniteColimits (etaleRestrictionSheaf ι AddCommGrpCat.{u})] :
    Epi (cohomologyRestrict ι F d) :=
  sorry

/-- Lemma 69.10.1 (3): étale cohomology with support in a closed subspace whose complement
is quasi-compact vanishes in degrees strictly larger than `dim X`. -/
@[stacks 0A4R]
theorem cohomologyWithSupport_isZero_of_dimension_le
    {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (d : ℕ) (hdim : dimension X ≤ d)
    (i : Z ⟶ X) [IsClosedImmersion i]
    [IsQuasiCompact (closedImmersionComplement i)]
    [∀ P : (smallEtaleSite Z)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallEtaleInclusion Z).op.HasPointwiseRightKanExtension P]
    (sectionsWithSupport :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u})
    (adj : sheafPushforward AddCommGrpCat.{u} i ⊣ sectionsWithSupport)
    (F : X.Modules) [F.IsQuasicoherent]
    {q : ℕ} (hq : d < q)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasSheafify (smallEtaleTopology Z) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u})]
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [sectionsWithSupport.Additive] :
    IsZero (cohomologyWithSupport i sectionsWithSupport adj F q) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
