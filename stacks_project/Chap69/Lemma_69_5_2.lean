module

public import Mathlib.CategoryTheory.Filtered.Basic
public import stacks_project.Chap66.Lemma_66_18_12_Pushforward
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact

/-!
# Lemma 69.5.2

Filtered colimits of abelian étale sheaves commute with higher direct images along a
quasi-compact quasi-separated morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImageFunctor`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical comparison `colim R^p f_* ℱ_i ⟶ R^p f_* (colim ℱ_i)` for abelian
sheaves on the small étale site. -/
noncomputable abbrev higherDirectImageColimitComparison
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [(sheafPushforward AddCommGrpCat.{u + 1} f).Additive]
    {I : Type (u + 1)} [Category.{u + 1} I] [IsFiltered I]
    (ℱ : I ⥤ Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [HasColimit ℱ] (p : ℕ)
    [HasColimit (ℱ ⋙ higherDirectImageFunctor f p)] :
    colimit (ℱ ⋙ higherDirectImageFunctor f p) ⟶
      (higherDirectImageFunctor f p).obj (colimit ℱ) :=
  colimit.post ℱ (higherDirectImageFunctor f p)

/-- The higher-direct-image colimit comparison is determined on each coprojection. -/
theorem higherDirectImageColimitComparison_ι
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [(sheafPushforward AddCommGrpCat.{u + 1} f).Additive]
    {I : Type (u + 1)} [Category.{u + 1} I] [IsFiltered I]
    (ℱ : I ⥤ Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [HasColimit ℱ] (p : ℕ)
    [HasColimit (ℱ ⋙ higherDirectImageFunctor f p)] (i : I) :
    colimit.ι (ℱ ⋙ higherDirectImageFunctor f p) i ≫
        higherDirectImageColimitComparison f ℱ p =
      (higherDirectImageFunctor f p).map (colimit.ι ℱ i) :=
  sorry

/-- Lemma 69.5.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a quasi-compact and
quasi-separated morphism of algebraic spaces over `S`. If `ℱ` is a filtered diagram of
abelian sheaves on `X_étale`, then for every `p : ℕ` the canonical comparison
`colim R^p f_* ℱ_i ⟶ R^p f_* (colim ℱ_i)` is an isomorphism. -/
@[stacks 07U6]
instance higherDirectImageFunctor_colimitComparison_isIso
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [(sheafPushforward AddCommGrpCat.{u + 1} f).Additive]
    {I : Type (u + 1)} [Category.{u + 1} I] [IsFiltered I]
    (ℱ : I ⥤ Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [HasColimit ℱ] (p : ℕ)
    [HasColimit (ℱ ⋙ higherDirectImageFunctor f p)] :
    IsIso (higherDirectImageColimitComparison f ℱ p) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
