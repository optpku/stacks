module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import stacks_project.Chap66.Lemma_66_18_8_Topos

/-!
# Small étale sheaf pullback for algebraic spaces

The contravariant pseudofunctor sending an algebraic space to its category of Type-valued
sheaves on the small étale site, with action given by inverse image of
`smallEtaleMorphismOfTopoi`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.EtaleSheaf

/-- Pullback of Type-valued sheaves along a morphism of small étale sites of algebraic
spaces. -/
noncomputable abbrev pullback {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology Y) (Type (u + 1)) ⥤
      Sheaf (smallEtaleTopology X) (Type (u + 1)) :=
  (smallEtaleMorphismOfTopoi f).inverseImage

/-- `pullback f` is the inverse image of `smallEtaleMorphismOfTopoi f`. -/
theorem pullback_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    pullback f = (smallEtaleMorphismOfTopoi f).inverseImage :=
  rfl

/-- Pullback of small étale sheaves along an identity is canonically the identity functor. -/
noncomputable def pullbackId {S : Scheme.{u}} (X : AlgebraicSpace S) :
    pullback (𝟙 X) ≅ 𝟭 (Sheaf (smallEtaleTopology X) (Type (u + 1))) :=
  let siteIso : spacesEtalePullback (𝟙 X) ≅ 𝟭 (spacesEtaleSite X) :=
    NatIso.ofComponents
      (fun V ↦
        MorphismProperty.Over.isoMk
          { hom := Limits.pullback.fst V.hom (𝟙 X)
            inv := Limits.pullback.lift (𝟙 V.left) V.hom
              ((Category.id_comp V.hom).trans (Category.comp_id V.hom).symm)
            hom_inv_id := sorry
            inv_hom_id := sorry }
          ((Limits.pullback.condition (f := V.hom) (g := 𝟙 X)).trans
            (Category.comp_id _)))
      (fun _ ↦ sorry)
  let spacesId : (spacesEtaleMorphismOfTopoi (𝟙 X)).inverseImage ≅
      𝟭 (Sheaf (spacesEtaleTopology X) (Type (u + 1))) :=
    Adjunction.leftAdjointIdIso
      ((spacesEtalePullback (𝟙 X)).sheafAdjunctionContinuous (Type (u + 1))
        (spacesEtaleTopology X) (spacesEtaleTopology X))
      (Functor.sheafPushforwardContinuousId' siteIso
        (Type (u + 1)) (spacesEtaleTopology X))
  let iX := smallEtaleInclusionDirectImage X
  Functor.isoWhiskerLeft iX (Functor.isoWhiskerRight spacesId iX.inv) ≪≫
    Functor.isoWhiskerLeft iX (Functor.leftUnitor iX.inv) ≪≫
    iX.asEquivalence.unitIso.symm

/-- Successive pullbacks of small étale sheaves are canonically pullback along the composite. -/
noncomputable def pullbackComp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ Z) (g : X ⟶ Y) :
    pullback f ⋙ pullback g ≅ pullback (g ≫ f) :=
  (smallEtaleMorphismOfTopoiComp g f).symm

/-- The contravariant pseudofunctor of Type-valued sheaves on small étale sites of
algebraic spaces. -/
noncomputable def pseudofunctor {S : Scheme.{u}} :
    Pseudofunctor (LocallyDiscrete (AlgebraicSpace S)ᵒᵖ) Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun X ↦ Cat.of (Sheaf (smallEtaleTopology X.unop) (Type (u + 1))))
    (fun f ↦ (pullback f.unop).toCatHom)
    (fun X ↦ Cat.Hom.isoMk (pullbackId X.unop))
    (fun f g ↦ Cat.Hom.isoMk (pullbackComp f.unop g.unop).symm)
    (fun _ _ _ ↦ sorry)
    (fun _ ↦ sorry)
    (fun _ ↦ sorry)

/-- The fiber of `pseudofunctor` at `X` is the category of Type-valued small étale sheaves. -/
theorem pseudofunctor_obj {S : Scheme.{u}} (X : AlgebraicSpace S) :
    pseudofunctor.obj (.mk (.op X)) =
      Cat.of (Sheaf (smallEtaleTopology X) (Type (u + 1))) :=
  sorry

/-- The action of `pseudofunctor` on a morphism of algebraic spaces is small étale sheaf
pullback. -/
theorem pseudofunctor_map {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (pseudofunctor.map f.op.toLoc).toFunctor = pullback f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.EtaleSheaf


