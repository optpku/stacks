module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Small
public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.EtaleSheaf

/-- Pullback of Type-valued sheaves along a morphism of small étale sites. -/
noncomputable abbrev pullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf Y.smallEtaleTopology (Type (u + 1)) ⥤
      Sheaf X.smallEtaleTopology (Type (u + 1)) :=
  (smallEtalePullback f).sheafPullback (Type (u + 1))
    Y.smallEtaleTopology X.smallEtaleTopology

/-- Pullback of small étale sheaves along an identity is canonically the identity functor. -/
noncomputable def pullbackId (X : Scheme.{u}) :
    pullback (𝟙 X) ≅ 𝟭 (Sheaf X.smallEtaleTopology (Type (u + 1))) :=
  let siteIso : smallEtalePullback (𝟙 X) ≅ 𝟭 X.Etale :=
    conjugateIsoEquiv
      (MorphismProperty.Over.mapPullbackAdj @Etale ⊤ (𝟙 X)
        (inferInstance : Etale (𝟙 X)) trivial)
      Adjunction.id
      (MorphismProperty.Over.mapId (P := @Etale) (Q := ⊤) X).symm
  let e := Adjunction.leftAdjointIdIso
    ((smallEtalePullback (𝟙 X)).sheafAdjunctionContinuous (Type (u + 1))
      X.smallEtaleTopology X.smallEtaleTopology)
    (Functor.sheafPushforwardContinuousId' siteIso
      (Type (u + 1)) X.smallEtaleTopology)
  NatIso.ofComponents (fun F ↦ e.app F) (fun _ ↦ sorry)

/-- Successive pullbacks of small étale sheaves are canonically pullback along the composite. -/
noncomputable def pullbackComp {X Y Z : Scheme.{u}} (f : Y ⟶ Z) (g : X ⟶ Y) :
    pullback f ⋙ pullback g ≅ pullback (g ≫ f) :=
  let siteIso : smallEtalePullback f ⋙ smallEtalePullback g ≅
      smallEtalePullback (g ≫ f) :=
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f).symm
  let e := Adjunction.leftAdjointCompIso
    ((smallEtalePullback f).sheafAdjunctionContinuous (Type (u + 1))
      Z.smallEtaleTopology Y.smallEtaleTopology)
    ((smallEtalePullback g).sheafAdjunctionContinuous (Type (u + 1))
      Y.smallEtaleTopology X.smallEtaleTopology)
    ((smallEtalePullback (g ≫ f)).sheafAdjunctionContinuous (Type (u + 1))
      Z.smallEtaleTopology X.smallEtaleTopology)
    (Functor.sheafPushforwardContinuousComp' siteIso
      (Type (u + 1)) Z.smallEtaleTopology Y.smallEtaleTopology
        X.smallEtaleTopology)
  NatIso.ofComponents (fun F ↦ e.app F) (fun _ ↦ sorry)

/-- The contravariant pseudofunctor of Type-valued sheaves on small étale sites. -/
noncomputable def pseudofunctor :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun X ↦ Cat.of (Sheaf X.unop.smallEtaleTopology (Type (u + 1))))
    (fun f ↦ (pullback f.unop).toCatHom)
    (fun X ↦ Cat.Hom.isoMk (pullbackId X.unop))
    (fun f g ↦ Cat.Hom.isoMk (pullbackComp f.unop g.unop).symm)
    (fun _ _ _ ↦ sorry)
    (fun _ ↦ sorry)
    (fun _ ↦ sorry)

/-- The fiber of `pseudofunctor` at `X` is the category of Type-valued small étale sheaves. -/
theorem pseudofunctor_obj (X : Scheme.{u}) :
    pseudofunctor.obj (.mk (.op X)) =
      Cat.of (Sheaf X.smallEtaleTopology (Type (u + 1))) := sorry

/-- The action of `pseudofunctor` on a scheme morphism is small étale sheaf pullback. -/
theorem pseudofunctor_map {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pseudofunctor.map f.op.toLoc).toFunctor = pullback f := sorry

/-- A section of a scheme morphism makes the canonical singleton descent-data functor an equivalence. -/
theorem descentIsEquivalenceOfSection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (split : SplitEpi f) :
    (pseudofunctor.toDescentData (fun _ : PUnit.{1} ↦ f)).IsEquivalence := sorry

end AlgebraicGeometry.Scheme.EtaleSheaf
