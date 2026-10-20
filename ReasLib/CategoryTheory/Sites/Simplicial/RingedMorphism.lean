/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.TotalMorphism
public import ReasLib.CategoryTheory.Sites.Grothendieck.SimplicialTotalMorphism
public import ReasLib.CategoryTheory.Sites.Topos.InternalRing
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom

/-!
# Morphisms of ringed simplicial sites

A morphism consists of a simplicial-site morphism and a homomorphism of ring sheaves.
The canonical ring-valued adjunction identifies its inverse-image and direct-image forms.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

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

/-- A morphism of ringed simplicial sites consists of a simplicial morphism and a
homomorphism from the inverse image of the target ring sheaf to the source ring sheaf. -/
abbrev RingedMorphism :=
  Σ h : {h : C' ⟶ C // IsMorphism J J' h ∧
      (∀ P : (totalSite C')ᵒᵖ ⥤ Type w, (IsMorphism.totalFunctor h).op.HasLeftKanExtension P)},
    (@IsMorphism.total _ _ J J' h.val inferInstance h.property.2).ringInverseImage.obj O' ⟶ O

namespace RingedMorphism

variable {J J' O O'}

/-- The natural transformation underlying a morphism of ringed simplicial sites. -/
def toSimplicial (f : RingedMorphism J J' O O') : C' ⟶ C :=
  f.1.val

/-- The underlying natural transformation is a morphism of simplicial sites. -/
instance isMorphism (f : RingedMorphism J J' O O') :
    IsMorphism J J' f.toSimplicial :=
  f.1.property.1

/-- The total functor of a ringed simplicial morphism has the required Kan extensions. -/
def hasLeftKanExtension_total (f : RingedMorphism J J' O O') :
    ∀ P : (totalSite C')ᵒᵖ ⥤ Type w,
      (IsMorphism.totalFunctor f.toSimplicial).op.HasLeftKanExtension P :=
  f.1.property.2

/-- The morphism of total topoi induced by a morphism of ringed simplicial sites. -/
def totalTopos (f : RingedMorphism J J' O O') :
    MorphismOfTopoiIn (topology C' J') (topology C J) :=
  @IsMorphism.total _ _ J J' f.toSimplicial inferInstance f.hasLeftKanExtension_total

/-- The homomorphism from the inverse image of the target ring sheaf to the source ring sheaf. -/
def structureMap (f : RingedMorphism J J' O O') :
    f.totalTopos.ringInverseImage.obj O' ⟶ O :=
  f.2

/-- The total ringed-topos morphism induced by a morphism of ringed simplicial sites. -/
def toToposHom (f : RingedMorphism J J' O O') :
    RingedSite.ToposHom (RingedSite.ofRingSheaf (topology C J) O) (RingedSite.ofRingSheaf (topology C' J') O') where
  toTopos := f.totalTopos
  structureMap := f.structureMap

/-- The underlying topos morphism of `toToposHom` is `f.totalTopos`. -/
theorem toToposHom_toTopos (f : RingedMorphism J J' O O') :
    (toToposHom f).toTopos = f.totalTopos :=
  rfl

/-- The inverse-image structure map of `toToposHom` is `f.structureMap`. -/
theorem toToposHom_structureMap (f : RingedMorphism J J' O O') :
    (toToposHom f).structureMap = f.structureMap :=
  rfl

/-- A simplicial morphism and an inverse-image ring homomorphism determine a ringed morphism. -/
def ofHom (h : C' ⟶ C) [IsMorphism J J' h]
    [∀ P : (totalSite C')ᵒᵖ ⥤ Type w, (IsMorphism.totalFunctor h).op.HasLeftKanExtension P]
    (hSharp : (IsMorphism.total J J' h).ringInverseImage.obj O' ⟶ O) :
    RingedMorphism J J' O O' :=
  ⟨⟨h, inferInstance, inferInstance⟩, hSharp⟩

/-- `ofHom` stores the given morphism of simplicial sites. -/
theorem ofHom_toSimplicial (h : C' ⟶ C) [IsMorphism J J' h]
    [∀ P : (totalSite C')ᵒᵖ ⥤ Type w, (IsMorphism.totalFunctor h).op.HasLeftKanExtension P]
    (hSharp : (IsMorphism.total J J' h).ringInverseImage.obj O' ⟶ O) :
    (ofHom h hSharp).toSimplicial = h :=
  rfl

/-- `ofHom` stores the given inverse-image homomorphism of sheaves of rings. -/
theorem ofHom_structureMap (h : C' ⟶ C) [IsMorphism J J' h]
    [∀ P : (totalSite C')ᵒᵖ ⥤ Type w, (IsMorphism.totalFunctor h).op.HasLeftKanExtension P]
    (hSharp : (IsMorphism.total J J' h).ringInverseImage.obj O' ⟶ O) :
    (ofHom h hSharp).structureMap = hSharp :=
  rfl

/-- Inverse-image homomorphisms `h_total⁻¹ O' ⟶ O` are equivalent to pushforward
homomorphisms `O' ⟶ h_total,* O`. -/
def structureMapEquiv (h : C' ⟶ C) [IsMorphism J J' h]
    [∀ P : (totalSite C')ᵒᵖ ⥤ Type w, (IsMorphism.totalFunctor h).op.HasLeftKanExtension P] :
    ((IsMorphism.total J J' h).ringInverseImage.obj O' ⟶ O) ≃
      (O' ⟶ (IsMorphism.total J J' h).ringDirectImage.obj O) :=
  (IsMorphism.total J J' h).ringAdjunction.homEquiv O' O

/-- The equivalent pushforward form `O' ⟶ h_total,* O` of the structure-sheaf map. -/
def directStructureMap (f : RingedMorphism J J' O O') :
    O' ⟶ f.totalTopos.ringDirectImage.obj O :=
  (f.totalTopos.ringAdjunction.homEquiv O' O) f.structureMap

/-- `directStructureMap` is the adjunct of `structureMap`. -/
theorem directStructureMap_eq_adjunct (f : RingedMorphism J J' O O') :
    directStructureMap f =
      (f.totalTopos.ringAdjunction.homEquiv O' O) f.structureMap :=
  rfl

/-- Reconstruct a morphism of ringed simplicial sites from the equivalent pushforward
homomorphism of sheaves of rings `O' ⟶ h_total,* O`. -/
def ofDirectImage {α : C' ⟶ C} [IsMorphism J J' α]
    [∀ P : (totalSite C')ᵒᵖ ⥤ Type w, (IsMorphism.totalFunctor α).op.HasLeftKanExtension P]
    (φ : O' ⟶ (IsMorphism.total J J' α).ringDirectImage.obj O) :
    RingedMorphism J J' O O' :=
  ofHom α (((IsMorphism.total J J' α).ringAdjunction.homEquiv O' O).symm φ)

/-- The inverse-image structure map of `ofDirectImage` is the adjunct of the given
pushforward homomorphism. -/
theorem ofDirectImage_structureMap {α : C' ⟶ C} [IsMorphism J J' α]
    [∀ P : (totalSite C')ᵒᵖ ⥤ Type w, (IsMorphism.totalFunctor α).op.HasLeftKanExtension P]
    (φ : O' ⟶ (IsMorphism.total J J' α).ringDirectImage.obj O) :
    (ofDirectImage φ).structureMap =
      ((IsMorphism.total J J' α).ringAdjunction.homEquiv O' O).symm φ :=
  rfl

/-- `ofDirectImage` stores the given simplicial-site morphism. -/
theorem ofDirectImage_toSimplicial {α : C' ⟶ C} [IsMorphism J J' α]
    [∀ P : (totalSite C')ᵒᵖ ⥤ Type w, (IsMorphism.totalFunctor α).op.HasLeftKanExtension P]
    (φ : O' ⟶ (IsMorphism.total J J' α).ringDirectImage.obj O) :
    (ofDirectImage φ).toSimplicial = α :=
  rfl

/-- Reconstructing from the adjunct pushforward map recovers `ofHom`. -/
theorem ofHom_eq_ofDirectImage (h : C' ⟶ C) [IsMorphism J J' h]
    [∀ P : (totalSite C')ᵒᵖ ⥤ Type w, (IsMorphism.totalFunctor h).op.HasLeftKanExtension P]
    (hSharp : (IsMorphism.total J J' h).ringInverseImage.obj O' ⟶ O) :
    ofHom h hSharp = ofDirectImage (structureMapEquiv h hSharp) :=
  sorry

section Identity

variable [∀ P : (totalSite C)ᵒᵖ ⥤ Type w,
    (IsMorphism.totalFunctor (𝟙 C)).op.HasLeftKanExtension P]

/-- The identity morphism of a ringed simplicial site in the covariant presentation. -/
def id : RingedMorphism J J O O :=
  let totalFunctor_idIso :
      IsMorphism.totalFunctor (𝟙 C) ≅ 𝟭 (totalSite C) :=
    eqToIso
      (congrArg
        (fun (G : Grothendieck (C ⋙ Cat.opFunctor.{v, u}) ⥤
            Grothendieck (C ⋙ Cat.opFunctor.{v, u})) ↦ G.op)
        ((congrArg Grothendieck.map
            (Functor.whiskerRight_id' (Cat.opFunctor.{v, u}))).trans
          Grothendieck.map_id_eq))
  let total_id_inverseImageIso :
      (IsMorphism.total J J (𝟙 C)).inverseImage ≅
        (MorphismOfTopoiIn.id (topology C J)).inverseImage :=
    Adjunction.leftAdjointUniq
      ((IsMorphism.total J J (𝟙 C)).adjunction.ofNatIsoRight
        (Functor.sheafPushforwardContinuousIso totalFunctor_idIso (Type w)
            (topology C J) (topology C J) ≪≫
          Functor.sheafPushforwardContinuousId (Type w) (topology C J)))
      (MorphismOfTopoiIn.id (topology C J)).adjunction
  ofHom (𝟙 C)
    ((MorphismOfTopoiIn.ringInverseImageNatIso total_id_inverseImageIso).hom.app O ≫
      (MorphismOfTopoiIn.ringInverseImageIdIso).hom.app O)

end Identity

end RingedMorphism

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable {F F' : SimplicialObject Cat.{v, u}}

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

/-- A morphism of ringed simplicial sites consists of a simplicial morphism and a
homomorphism from the inverse image of the target ring sheaf to the source ring sheaf. -/
abbrev RingedMorphism :=
  Σ h : {h : F ⟶ F' // IsFiberwiseMorphism J J' h ∧
      (∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w, (Grothendieck.map h).op.HasPointwiseRightKanExtension P)},
    (@IsFiberwiseMorphism.total _ _ J J' h.val inferInstance h.property.2).ringInverseImage.obj O' ⟶ O

namespace RingedMorphism

variable {J J' O O'}

/-- The natural transformation underlying a morphism of ringed simplicial sites. -/
def toSimplicial (f : RingedMorphism J J' O O') : F ⟶ F' :=
  f.1.val

/-- The underlying natural transformation is a morphism of simplicial sites. -/
instance isMorphism (f : RingedMorphism J J' O O') :
    IsFiberwiseMorphism J J' f.toSimplicial :=
  f.1.property.1

/-- The total functor of a ringed simplicial morphism has the required Kan extensions. -/
def hasPointwiseRightKanExtension_total (f : RingedMorphism J J' O O') :
    ∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
      (Grothendieck.map f.toSimplicial).op.HasPointwiseRightKanExtension P :=
  f.1.property.2

/-- The morphism of total topoi induced by a morphism of ringed simplicial sites. -/
def totalTopos (f : RingedMorphism J J' O O') :
    MorphismOfTopoiIn (topology F' J') (topology F J) :=
  @IsFiberwiseMorphism.total _ _ J J' f.toSimplicial inferInstance f.hasPointwiseRightKanExtension_total

/-- The homomorphism from the inverse image of the target ring sheaf to the source ring sheaf. -/
def structureMap (f : RingedMorphism J J' O O') :
    f.totalTopos.ringInverseImage.obj O' ⟶ O :=
  f.2

/-- The total ringed-topos morphism induced by a morphism of ringed simplicial sites. -/
def toToposHom (f : RingedMorphism J J' O O') :
    RingedSite.ToposHom (RingedSite.ofRingSheaf (topology F J) O) (RingedSite.ofRingSheaf (topology F' J') O') where
  toTopos := f.totalTopos
  structureMap := f.structureMap

/-- The underlying topos morphism of `toToposHom` is `f.totalTopos`. -/
theorem toToposHom_toTopos (f : RingedMorphism J J' O O') :
    (toToposHom f).toTopos = f.totalTopos :=
  rfl

/-- The inverse-image structure map of `toToposHom` is `f.structureMap`. -/
theorem toToposHom_structureMap (f : RingedMorphism J J' O O') :
    (toToposHom f).structureMap = f.structureMap :=
  rfl

/-- A simplicial morphism and an inverse-image ring homomorphism determine a ringed morphism. -/
def ofHom (h : F ⟶ F') [IsFiberwiseMorphism J J' h]
    [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
      (Grothendieck.map h).op.HasPointwiseRightKanExtension P]
    (hSharp : (IsFiberwiseMorphism.total J J' h).ringInverseImage.obj O' ⟶ O) :
    RingedMorphism J J' O O' :=
  ⟨⟨h, inferInstance, inferInstance⟩, hSharp⟩

/-- `ofHom` stores the given morphism of simplicial sites. -/
theorem ofHom_toSimplicial (h : F ⟶ F') [IsFiberwiseMorphism J J' h]
    [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
      (Grothendieck.map h).op.HasPointwiseRightKanExtension P]
    (hSharp : (IsFiberwiseMorphism.total J J' h).ringInverseImage.obj O' ⟶ O) :
    (ofHom h hSharp).toSimplicial = h :=
  rfl

/-- `ofHom` stores the given inverse-image homomorphism of sheaves of rings. -/
theorem ofHom_structureMap (h : F ⟶ F') [IsFiberwiseMorphism J J' h]
    [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
      (Grothendieck.map h).op.HasPointwiseRightKanExtension P]
    (hSharp : (IsFiberwiseMorphism.total J J' h).ringInverseImage.obj O' ⟶ O) :
    (ofHom h hSharp).structureMap = hSharp :=
  rfl

/-- Inverse-image homomorphisms `h_total⁻¹ O' ⟶ O` are equivalent to pushforward
homomorphisms `O' ⟶ h_total,* O`. -/
def structureMapEquiv (h : F ⟶ F') [IsFiberwiseMorphism J J' h]
    [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
      (Grothendieck.map h).op.HasPointwiseRightKanExtension P] :
    ((IsFiberwiseMorphism.total J J' h).ringInverseImage.obj O' ⟶ O) ≃
      (O' ⟶ (IsFiberwiseMorphism.total J J' h).ringDirectImage.obj O) :=
  (IsFiberwiseMorphism.total J J' h).ringAdjunction.homEquiv O' O

/-- The equivalent pushforward form `O' ⟶ h_total,* O` of the structure-sheaf map. -/
def directStructureMap (f : RingedMorphism J J' O O') :
    O' ⟶ f.totalTopos.ringDirectImage.obj O :=
  (f.totalTopos.ringAdjunction.homEquiv O' O) f.structureMap

/-- `directStructureMap` is the adjunct of `structureMap`. -/
theorem directStructureMap_eq_adjunct (f : RingedMorphism J J' O O') :
    directStructureMap f =
      (f.totalTopos.ringAdjunction.homEquiv O' O) f.structureMap :=
  rfl

/-- Reconstruct a morphism of ringed simplicial sites from the equivalent pushforward
homomorphism of sheaves of rings `O' ⟶ h_total,* O`. -/
def ofDirectImage {α : F ⟶ F'} [IsFiberwiseMorphism J J' α]
    [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
      (Grothendieck.map α).op.HasPointwiseRightKanExtension P]
    (φ : O' ⟶ (IsFiberwiseMorphism.total J J' α).ringDirectImage.obj O) :
    RingedMorphism J J' O O' :=
  ofHom α (((IsFiberwiseMorphism.total J J' α).ringAdjunction.homEquiv O' O).symm φ)

/-- The inverse-image structure map of `ofDirectImage` is the adjunct of the given
pushforward homomorphism. -/
theorem ofDirectImage_structureMap {α : F ⟶ F'} [IsFiberwiseMorphism J J' α]
    [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
      (Grothendieck.map α).op.HasPointwiseRightKanExtension P]
    (φ : O' ⟶ (IsFiberwiseMorphism.total J J' α).ringDirectImage.obj O) :
    (ofDirectImage φ).structureMap =
      ((IsFiberwiseMorphism.total J J' α).ringAdjunction.homEquiv O' O).symm φ :=
  rfl

/-- `ofDirectImage` stores the given simplicial-site morphism. -/
theorem ofDirectImage_toSimplicial {α : F ⟶ F'} [IsFiberwiseMorphism J J' α]
    [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
      (Grothendieck.map α).op.HasPointwiseRightKanExtension P]
    (φ : O' ⟶ (IsFiberwiseMorphism.total J J' α).ringDirectImage.obj O) :
    (ofDirectImage φ).toSimplicial = α :=
  rfl

/-- Reconstructing from the adjunct pushforward map recovers `ofHom`. -/
theorem ofHom_eq_ofDirectImage (h : F ⟶ F') [IsFiberwiseMorphism J J' h]
    [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
      (Grothendieck.map h).op.HasPointwiseRightKanExtension P]
    (hSharp : (IsFiberwiseMorphism.total J J' h).ringInverseImage.obj O' ⟶ O) :
    ofHom h hSharp = ofDirectImage (structureMapEquiv h hSharp) :=
  sorry

section Identity

variable [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
    (Grothendieck.map (𝟙 F)).op.HasPointwiseRightKanExtension P]
variable [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
    (𝟭 (Grothendieck F)).op.HasPointwiseRightKanExtension P]

/-- The identity morphism of a ringed simplicial site in the fiberwise presentation. -/
def id : RingedMorphism J J O O :=
  let totalFunctor_idIso :
      Grothendieck.map (𝟙 F) ≅ 𝟭 (Grothendieck F) :=
    eqToIso map_id_eq
  let total_id_inverseImageIso :
      (IsFiberwiseMorphism.total J J (𝟙 F)).inverseImage ≅
        (MorphismOfTopoiIn.id (topology F J)).inverseImage :=
    Adjunction.leftAdjointUniq
      ((IsFiberwiseMorphism.total J J (𝟙 F)).adjunction.ofNatIsoRight
        (Functor.sheafPushforwardCocontinuousIso (topology F J) (topology F J)
            (Grothendieck.map (𝟙 F)) totalFunctor_idIso ≪≫
          Functor.sheafPushforwardCocontinuousId (Type w) (topology F J)))
      (MorphismOfTopoiIn.id (topology F J)).adjunction
  ofHom (𝟙 F)
    ((MorphismOfTopoiIn.ringInverseImageNatIso total_id_inverseImageIso).hom.app O ≫
      (MorphismOfTopoiIn.ringInverseImageIdIso).hom.app O)

end Identity

end RingedMorphism

end CategoryTheory.Grothendieck
