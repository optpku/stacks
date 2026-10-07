module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import stacks_project.Chap85.Lemma_85_6_1_Fiber
public import stacks_project.Chap85.Remark_85_5_1_Morphism

/-!
# Morphisms of ringed simplicial sites (case B)

A morphism of ringed simplicial sites in Situation 85.3.3 case B is a pair
`(h, hSharp)`: an unringed fiberwise morphism of simplicial sites `α : F ⟶ F'`
as in `IsFiberwiseMorphism`, together with a homomorphism of sheaves of rings
`h_total⁻¹ O' ⟶ O` along the totalization of `α`.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite
open scoped MorphismOfTopoiIn

noncomputable section

namespace CategoryTheory.Grothendieck

variable {F F' : SimplicialObject Cat.{v, u}}

/-- Cocontinuous sheaf pushforward along the identity functor of a site is the identity
on sheaves. -/
def sheafPushforwardCocontinuous_id
    {C : Type u} [Category.{v} C] (K : GrothendieckTopology C)
    [∀ P : Cᵒᵖ ⥤ Type w, (𝟭 C).op.HasPointwiseRightKanExtension P] :
    (𝟭 C).sheafPushforwardCocontinuous (Type w) K K ≅ 𝟭 (Sheaf K (Type w)) :=
  Functor.fullyFaithfulCancelRight (sheafToPresheaf K (Type w))
    (((𝟭 C).sheafPushforwardCocontinuousCompSheafToPresheafIso (Type w) K K).trans
      ((NatIso.hcomp (Iso.refl (sheafToPresheaf K (Type w)))
          ((((𝟭 C).op.ranAdjunction (Type w)).ofNatIsoLeft
              (eqToIso Functor.whiskeringLeft_obj_id)).rightAdjointUniq
            (Adjunction.id : 𝟭 (Cᵒᵖ ⥤ Type w) ⊣ 𝟭 (Cᵒᵖ ⥤ Type w)))).trans
        (Functor.rightUnitor (sheafToPresheaf K (Type w)))))

/-- The identity comparison of `sheafPushforwardCocontinuous_id` is invertible on each sheaf. -/
theorem sheafPushforwardCocontinuous_id_hom_inv
    {C : Type u} [Category.{v} C] (K : GrothendieckTopology C)
    [∀ P : Cᵒᵖ ⥤ Type w, (𝟭 C).op.HasPointwiseRightKanExtension P]
    (G : Sheaf K (Type w)) :
    (sheafPushforwardCocontinuous_id K).hom.app G ≫
      (sheafPushforwardCocontinuous_id K).inv.app G = 𝟙 _ :=
  sorry

variable (J : ∀ n, Precoverage (F.obj n)) (J' : ∀ n, Precoverage (F'.obj n))
variable [IsFiberwiseSite F J] [IsFiberwiseSite F' J']
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasSheafify (J' n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [HasSheafify (topology F' J') (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [HasWeakSheafify (topology F' J') (Type w)]
variable (O : Sheaf (topology F J) RingCat.{w})
variable (O' : Sheaf (topology F' J') RingCat.{w})
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(topology F' J').HasSheafCompose (CategoryTheory.forget RingCat.{w})]

namespace RingedMorphism

/-- The functor `v_total : C_total ⥤ C'_total` obtained by applying the component functors
of a fiberwise morphism of simplicial sites in each degree. -/
def totalFunctor (α : F ⟶ F') : Grothendieck F ⥤ Grothendieck F' :=
  Grothendieck.map α

/-- `v_total` is cocontinuous for the identity-degree total topologies. -/
instance instIsCocontinuous_totalFunctor (α : F ⟶ F') [IsFiberwiseMorphism J J' α] :
    (totalFunctor α).IsCocontinuous (topology F J) (topology F' J') :=
  sorry

/-- The morphism of topoi `h_total : Sh(C_total) ⟶ Sh(C'_total)` presented by `totalFunctor`. -/
def total (α : F ⟶ F') [IsFiberwiseMorphism J J' α]
    [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
      (totalFunctor α).op.HasPointwiseRightKanExtension P] :
    MorphismOfTopoiIn (topology F' J') (topology F J) :=
  (totalFunctor α).morphismOfTopoiInOfCocontinuous (topology F J) (topology F' J')

/-- Inverse image of `total` is cocontinuous sheaf pullback along `v_total`. -/
theorem total_inverseImage (α : F ⟶ F') [IsFiberwiseMorphism J J' α]
    [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
      (totalFunctor α).op.HasPointwiseRightKanExtension P] :
    (total J J' α).inverseImage =
      (totalFunctor α).sheafPullbackCocontinuous (Type w) (topology F J) (topology F' J') :=
  sorry

/-- Direct image of `total` is cocontinuous sheaf pushforward along `v_total`. -/
theorem total_pushforward (α : F ⟶ F') [IsFiberwiseMorphism J J' α]
    [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
      (totalFunctor α).op.HasPointwiseRightKanExtension P] :
    (total J J' α).pushforward =
      (totalFunctor α).sheafPushforwardCocontinuous (Type w) (topology F J) (topology F' J') :=
  sorry

/-- The identity transformation totalizes to a functor isomorphic to the identity of the
total category. -/
theorem totalFunctor_id_obj (X : Grothendieck F) :
    (totalFunctor (𝟙 F)).obj X = (𝟭 (Grothendieck F)).obj X :=
  sorry

end RingedMorphism

/-- A morphism of ringed simplicial sites in the fiberwise (case B) presentation: a morphism
of simplicial sites `α : F ⟶ F'` together with a homomorphism of sheaves of rings
`h_total⁻¹ O' ⟶ O`. -/
structure RingedMorphism where
  /-- The underlying morphism of simplicial sites, as a natural transformation
  `α : F ⟶ F'` whose components are cocontinuous functors. -/
  toSimplicial : F ⟶ F'
  [isMorphism : IsFiberwiseMorphism J J' toSimplicial]
  [hasPointwiseRightKanExtension_total :
      ∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
        (RingedMorphism.totalFunctor toSimplicial).op.HasPointwiseRightKanExtension P]
  /-- The homomorphism of sheaves of rings `h_total⁻¹ O' ⟶ O`. -/
  structureMap :
    (RingedMorphism.total J J' toSimplicial).ringInverseImage.obj O' ⟶ O

attribute [instance] RingedMorphism.isMorphism
attribute [instance] RingedMorphism.hasPointwiseRightKanExtension_total

namespace RingedMorphism

variable {J J' O O'}
variable [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
    (totalFunctor (𝟙 F)).op.HasPointwiseRightKanExtension P]
variable [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
    (𝟭 (Grothendieck F)).op.HasPointwiseRightKanExtension P]

/-- The identity transformation of a fiberwise simplicial site totalizes to a functor
isomorphic to the identity of the total category. -/
def totalFunctor_idIso :
    totalFunctor (𝟙 F) ≅ 𝟭 (Grothendieck F) :=
  eqToIso map_id_eq

/-- Inverse image along `h_total` of the identity morphism of simplicial sites is canonically
isomorphic to the identity inverse image. -/
def total_id_inverseImageIso :
    (total J J (𝟙 F)).inverseImage ≅
      (MorphismOfTopoiIn.id (topology F J)).inverseImage :=
  Adjunction.leftAdjointUniq
    ((total J J (𝟙 F)).adjunction.ofNatIsoRight
      (Functor.sheafPushforwardCocontinuousIso (topology F J) (topology F J)
          (totalFunctor (𝟙 F)) totalFunctor_idIso ≪≫
        sheafPushforwardCocontinuous_id (topology F J)))
    (MorphismOfTopoiIn.id (topology F J)).adjunction

/-- The identity morphism of a ringed simplicial site in the fiberwise presentation. -/
def id : RingedMorphism J J O O where
  toSimplicial := 𝟙 F
  structureMap :=
    (MorphismOfTopoiIn.ringInverseImageNatIso total_id_inverseImageIso).hom.app O ≫
      (MorphismOfTopoiIn.ringInverseImageIdIso).hom.app O

/-- The morphism of ringed topoi `h_total : (Sh(C_total), O) ⟶ (Sh(C'_total), O')` attached
to a morphism of ringed simplicial sites. -/
def toToposHom (f : RingedMorphism J J' O O') :
    ToposHom (fiberTotalRingedSite F J O) (fiberTotalRingedSite F' J' O') where
  toTopos := total J J' f.toSimplicial
  structureMap := f.structureMap

/-- The underlying topos morphism of `toToposHom` is `total`. -/
theorem toToposHom_toTopos (f : RingedMorphism J J' O O') :
    (toToposHom f).toTopos = total J J' f.toSimplicial :=
  sorry

/-- The inverse-image structure map of `toToposHom` is `f.structureMap`. -/
theorem toToposHom_structureMap (f : RingedMorphism J J' O O') :
    (toToposHom f).structureMap = f.structureMap :=
  sorry

/-- The equivalent pushforward form `O' ⟶ h_total,* O` of the structure-sheaf map. -/
def directStructureMap (f : RingedMorphism J J' O O') :
    O' ⟶ (total J J' f.toSimplicial).ringDirectImage.obj O :=
  ((total J J' f.toSimplicial).ringAdjunction.homEquiv O' O) f.structureMap

/-- `directStructureMap` is the adjunct of `structureMap`. -/
theorem directStructureMap_eq_adjunct (f : RingedMorphism J J' O O') :
    directStructureMap f =
      ((total J J' f.toSimplicial).ringAdjunction.homEquiv O' O) f.structureMap :=
  sorry

/-- Reconstruct a morphism of ringed simplicial sites from the equivalent pushforward
homomorphism of sheaves of rings `O' ⟶ h_total,* O`. -/
def ofDirectImage {α : F ⟶ F'} [IsFiberwiseMorphism J J' α]
    [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
      (totalFunctor α).op.HasPointwiseRightKanExtension P]
    (φ : O' ⟶ (total J J' α).ringDirectImage.obj O) :
    RingedMorphism J J' O O' where
  toSimplicial := α
  structureMap := ((total J J' α).ringAdjunction.homEquiv O' O).symm φ

/-- The inverse-image structure map of `ofDirectImage` is the adjunct of the given
pushforward homomorphism. -/
theorem ofDirectImage_structureMap {α : F ⟶ F'} [IsFiberwiseMorphism J J' α]
    [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
      (totalFunctor α).op.HasPointwiseRightKanExtension P]
    (φ : O' ⟶ (total J J' α).ringDirectImage.obj O) :
    (ofDirectImage φ).structureMap =
      ((total J J' α).ringAdjunction.homEquiv O' O).symm φ :=
  sorry

/-- `ofDirectImage` stores the given simplicial-site morphism. -/
theorem ofDirectImage_toSimplicial {α : F ⟶ F'} [IsFiberwiseMorphism J J' α]
    [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
      (totalFunctor α).op.HasPointwiseRightKanExtension P]
    (φ : O' ⟶ (total J J' α).ringDirectImage.obj O) :
    (ofDirectImage φ).toSimplicial = α :=
  sorry

end RingedMorphism

end CategoryTheory.Grothendieck
