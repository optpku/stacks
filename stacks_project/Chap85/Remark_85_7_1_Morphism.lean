/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import stacks_project.Chap85.Lemma_85_6_1_Ringed
public import stacks_project.Chap85.Remark_85_5_1_Morphism

/-!
# Morphisms of ringed simplicial sites (case A)

A morphism of ringed simplicial sites in Situation 85.3.3 case A is a pair
`(h, hSharp)`: an unringed morphism of simplicial sites `α : C' ⟶ C` as in
`IsMorphism`, together with a homomorphism of sheaves of rings
`h_total⁻¹ O' ⟶ O` along the totalization of `α`.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite
open scoped MorphismOfTopoiIn

noncomputable section

namespace CategoryTheory.SimplicialSites

variable {C C' : SimplexCategory ⥤ Cat.{v, u}}
variable (J : ∀ n, Precoverage (C.obj n)) (J' : ∀ n, Precoverage (C'.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J' n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C'.obj m)ᵒᵖ ⥤ Type w),
    ((C'.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J] [IsMorphismDiagram C' J']
variable [HasWeakSheafify (topology C J) (Type w)]
variable [HasWeakSheafify (topology C' J') (Type w)]
variable (O : Sheaf (topology C J) RingCat.{w})
variable (O' : Sheaf (topology C' J') RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [(topology C' J').HasSheafCompose (forget RingCat.{w})]

namespace RingedMorphism

/-- The functor `v_total : C'_total ⥤ C_total` obtained by applying the component functors
of a morphism of simplicial sites in each degree. -/
def totalFunctor (α : C' ⟶ C) : totalSite C' ⥤ totalSite C :=
  (Grothendieck.map (Functor.whiskerRight α Cat.opFunctor.{v, u})).op

/-- `v_total` is continuous for the identity-simplex total topologies. -/
instance instIsContinuous_totalFunctor (α : C' ⟶ C) [IsMorphism J J' α] :
    (totalFunctor α).IsContinuous (topology C' J') (topology C J) :=
  sorry

/-- Inverse image along `v_total` preserves finite limits, so `h_total` is a morphism of topoi. -/
instance instPreservesFiniteLimits_totalSheafPullback (α : C' ⟶ C) [IsMorphism J J' α]
    [∀ P : (totalSite C')ᵒᵖ ⥤ Type w, (totalFunctor α).op.HasLeftKanExtension P] :
    PreservesFiniteLimits
      ((totalFunctor α).sheafPullback (Type w) (topology C' J') (topology C J)) :=
  sorry

/-- The morphism of topoi `h_total : Sh(C_total) ⟶ Sh(C'_total)` presented by `totalFunctor`. -/
def total (α : C' ⟶ C) [IsMorphism J J' α]
    [∀ P : (totalSite C')ᵒᵖ ⥤ Type w, (totalFunctor α).op.HasLeftKanExtension P] :
    MorphismOfTopoiIn (topology C' J') (topology C J) :=
  (totalFunctor α).morphismOfTopoiInOfContinuous (topology C' J') (topology C J)

/-- Inverse image of `total` is sheaf pullback along `v_total`. -/
theorem total_inverseImage (α : C' ⟶ C) [IsMorphism J J' α]
    [∀ P : (totalSite C')ᵒᵖ ⥤ Type w, (totalFunctor α).op.HasLeftKanExtension P] :
    (total J J' α).inverseImage =
      (totalFunctor α).sheafPullback (Type w) (topology C' J') (topology C J) :=
  sorry

/-- Direct image of `total` is continuous sheaf pushforward along `v_total`. -/
theorem total_pushforward (α : C' ⟶ C) [IsMorphism J J' α]
    [∀ P : (totalSite C')ᵒᵖ ⥤ Type w, (totalFunctor α).op.HasLeftKanExtension P] :
    (total J J' α).pushforward =
      (totalFunctor α).sheafPushforwardContinuous (Type w) (topology C' J') (topology C J) :=
  sorry

/-- The identity transformation totalizes to a functor isomorphic to the identity of the
total site. -/
theorem totalFunctor_id_obj (X : totalSite C) :
    (totalFunctor (𝟙 C)).obj X = (𝟭 (totalSite C)).obj X :=
  sorry

end RingedMorphism

/-- A morphism of ringed simplicial sites in the covariant (case A) presentation: a morphism
of simplicial sites `α : C' ⟶ C` together with a homomorphism of sheaves of rings
`h_total⁻¹ O' ⟶ O`. -/
structure RingedMorphism where
  /-- The underlying morphism of simplicial sites, as a natural transformation
  `α : C' ⟶ C` whose components are exact morphisms of sites. -/
  toSimplicial : C' ⟶ C
  [isMorphism : IsMorphism J J' toSimplicial]
  [hasLeftKanExtension_total :
      ∀ P : (totalSite C')ᵒᵖ ⥤ Type w,
        (RingedMorphism.totalFunctor toSimplicial).op.HasLeftKanExtension P]
  /-- The homomorphism of sheaves of rings `h_total⁻¹ O' ⟶ O`. -/
  structureMap :
    (RingedMorphism.total J J' toSimplicial).ringInverseImage.obj O' ⟶ O

attribute [instance] RingedMorphism.isMorphism
attribute [instance] RingedMorphism.hasLeftKanExtension_total

namespace RingedMorphism

variable {J J' O O'}
variable [∀ P : (totalSite C)ᵒᵖ ⥤ Type w,
    (totalFunctor (𝟙 C)).op.HasLeftKanExtension P]

/-- The identity transformation of a covariant simplex diagram totalizes to a functor
isomorphic to the identity of the total site. -/
def totalFunctor_idIso :
    totalFunctor (𝟙 C) ≅ 𝟭 (totalSite C) :=
  eqToIso
    (congrArg
      (fun (G : Grothendieck (C ⋙ Cat.opFunctor.{v, u}) ⥤
          Grothendieck (C ⋙ Cat.opFunctor.{v, u})) ↦ G.op)
      ((congrArg Grothendieck.map
          (Functor.whiskerRight_id' (Cat.opFunctor.{v, u}))).trans
        Grothendieck.map_id_eq))

/-- Inverse image along `h_total` of the identity morphism of simplicial sites is canonically
isomorphic to the identity inverse image. -/
def total_id_inverseImageIso :
    (total J J (𝟙 C)).inverseImage ≅
      (MorphismOfTopoiIn.id (topology C J)).inverseImage :=
  Adjunction.leftAdjointUniq
    ((total J J (𝟙 C)).adjunction.ofNatIsoRight
      (Functor.sheafPushforwardContinuousIso totalFunctor_idIso (Type w)
          (topology C J) (topology C J) ≪≫
        Functor.sheafPushforwardContinuousId (Type w) (topology C J)))
    (MorphismOfTopoiIn.id (topology C J)).adjunction

/-- The identity morphism of a ringed simplicial site in the covariant presentation. -/
def id : RingedMorphism J J O O where
  toSimplicial := 𝟙 C
  structureMap :=
    (MorphismOfTopoiIn.ringInverseImageNatIso total_id_inverseImageIso).hom.app O ≫
      (MorphismOfTopoiIn.ringInverseImageIdIso).hom.app O

/-- The morphism of ringed topoi `h_total : (Sh(C_total), O) ⟶ (Sh(C'_total), O')` attached
to a morphism of ringed simplicial sites. -/
def toToposHom (f : RingedMorphism J J' O O') :
    ToposHom (totalRingedSite C J O) (totalRingedSite C' J' O') where
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
def ofDirectImage {α : C' ⟶ C} [IsMorphism J J' α]
    [∀ P : (totalSite C')ᵒᵖ ⥤ Type w, (totalFunctor α).op.HasLeftKanExtension P]
    (φ : O' ⟶ (total J J' α).ringDirectImage.obj O) :
    RingedMorphism J J' O O' where
  toSimplicial := α
  structureMap := ((total J J' α).ringAdjunction.homEquiv O' O).symm φ

/-- The inverse-image structure map of `ofDirectImage` is the adjunct of the given
pushforward homomorphism. -/
theorem ofDirectImage_structureMap {α : C' ⟶ C} [IsMorphism J J' α]
    [∀ P : (totalSite C')ᵒᵖ ⥤ Type w, (totalFunctor α).op.HasLeftKanExtension P]
    (φ : O' ⟶ (total J J' α).ringDirectImage.obj O) :
    (ofDirectImage φ).structureMap =
      ((total J J' α).ringAdjunction.homEquiv O' O).symm φ :=
  sorry

/-- `ofDirectImage` stores the given simplicial-site morphism. -/
theorem ofDirectImage_toSimplicial {α : C' ⟶ C} [IsMorphism J J' α]
    [∀ P : (totalSite C')ᵒᵖ ⥤ Type w, (totalFunctor α).op.HasLeftKanExtension P]
    (φ : O' ⟶ (total J J' α).ringDirectImage.obj O) :
    (ofDirectImage φ).toSimplicial = α :=
  sorry

end RingedMorphism

end CategoryTheory.SimplicialSites
