/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ModuleSheaf
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Identity

@[expose] public section

section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry

noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- The small-étale pullback functor of an identity, using the adjunction of over categories. -/
def smallEtaleIdentityIso (S : Scheme.{u}) : smallEtalePullback (𝟙 S) ≅ 𝟭 S.Etale :=
  conjugateIsoEquiv
    (MorphismProperty.Over.mapPullbackAdj @Etale ⊤ (𝟙 S)
      (inferInstance : Etale (𝟙 S)) trivial)
    Adjunction.id (MorphismProperty.Over.mapId (P := @Etale) (Q := ⊤) S).symm

/-- Pullback along the identity has the explicit identity-site equivalence. -/
instance smallEtaleIdentity_isEquivalence (S : Scheme.{u}) :
    (smallEtalePullback (𝟙 S)).IsEquivalence :=
  Functor.isEquivalence_of_iso (smallEtaleIdentityIso S).symm

variable (S : Scheme.{u}) (Λ : Type u) [CommRing Λ]
  [HasWeakSheafify S.smallEtaleTopology (ModuleCat.{u} Λ)]

/-- The canonical identity comparison for module inverse image, from uniqueness of adjoints. -/
def moduleInverseImageIdentityIso :
    (Sheaf.smallEtaleInverseImage (𝟙 S) (ModuleCat.{u} Λ)) ≅ 𝟭 (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  Adjunction.leftAdjointIdIso
    ((smallEtalePullback (𝟙 S)).sheafAdjunctionContinuous (ModuleCat.{u} Λ)
      S.smallEtaleTopology S.smallEtaleTopology)
    (Functor.sheafPushforwardContinuousId' (smallEtaleIdentityIso S)
      (ModuleCat.{u} Λ) S.smallEtaleTopology)

variable [∀ U : S.Etale,
    HasWeakSheafify (S.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Derived identity comparison, induced by the actual module-sheaf identity comparison. -/
def derivedInverseImageIdentityIso :
    etaleModuleDerivedInverseImage (𝟙 S) Λ ≅ 𝟭 ((DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)))) :=
  Functor.MapDerivedCategory.functorIso (moduleInverseImageIdentityIso S Λ) ≪≫
    ExactFunctor.MapDerivedCategory.idFunctorIso (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))

end AlgebraicGeometry.Scheme.Etale

end
end

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section
universe u v w

namespace AlgebraicGeometry.Scheme.Etale

/-- The small-etale equivalence uses pullback along the given isomorphism and its inverse. -/
def smallEtaleAmbientEquivalence {T T' : Scheme.{u}} (e : T' ≅ T) : T.Etale ≌ T'.Etale :=
  CategoryTheory.Equivalence.mk (smallEtalePullback e.hom) (smallEtalePullback e.inv)
    ((smallEtalePullbackCompIso e.inv e.hom ≪≫
      eqToIso (congrArg smallEtalePullback e.inv_hom_id) ≪≫ smallEtaleIdentityIso T).symm)
    (smallEtalePullbackCompIso e.hom e.inv ≪≫
      eqToIso (congrArg smallEtalePullback e.hom_inv_id) ≪≫ smallEtaleIdentityIso T')

/-- Transfer the given Kan extension through the actual ambient equivalence over the base. -/
theorem smallEtaleAmbient_hasLeftKanExtension
    {Y T T' : Scheme.{u}} (p : T ⟶ Y) (p' : T' ⟶ Y)
    (e : T' ≅ T) (hp : e.hom ≫ p = p')
    {A : Type v} [Category.{w} A] (F : Y.Etaleᵒᵖ ⥤ A)
    [(smallEtalePullback p).op.HasLeftKanExtension F] :
    (smallEtalePullback p').op.HasLeftKanExtension F := by
  -- Local instance justification (proof-local temporary data): Use the explicitly constructed small-etale equivalence of this fixed e, whose inverse is pullback along e.inv.
  letI : (smallEtalePullback e.hom).IsEquivalence :=
    (smallEtaleAmbientEquivalence e).isEquivalence_functor
  let comparison : smallEtalePullback p ⋙ smallEtalePullback e.hom ≅ smallEtalePullback p' :=
    smallEtalePullbackCompIso e.hom p ≪≫ eqToIso (congrArg smallEtalePullback hp)
  let comparisonOp : (smallEtalePullback p).op ⋙ (smallEtalePullback e.hom).op ≅
      (smallEtalePullback p').op :=
    (Functor.opComp (smallEtalePullback p) (smallEtalePullback e.hom)).symm ≪≫
      NatIso.op comparison.symm
  exact (Functor.hasLeftExtension_iff_postcomp₁ comparisonOp F).2 inferInstance

end AlgebraicGeometry.Scheme.Etale
end

namespace AlgebraicGeometry.Scheme.Etale
/-- Kan extension along an isomorphism of small étale sites exists:
the inverse equivalence supplies its fixed universal-property model. -/
instance smallEtaleIso_hasLeftKanExtension {S T : Scheme.{u}} (f : S ⟶ T) [IsIso f]
    (A : Type v) [Category.{w} A] (F : T.Etaleᵒᵖ ⥤ A) :
    (smallEtalePullback f).op.HasLeftKanExtension F := sorry

/-- Every coefficient functor preserves Kan extension along a site equivalence. -/
instance smallEtaleIso_preservesLeftKanExtensions {S T : Scheme.{u}} (f : S ⟶ T) [IsIso f]
    (Λ : Type u) [CommRing Λ] :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (smallEtalePullback f).op := sorry

end AlgebraicGeometry.Scheme.Etale
