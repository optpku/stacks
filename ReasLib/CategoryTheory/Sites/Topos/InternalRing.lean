module

public import ReasLib.Algebra.Category.Ring.Sheaf.Internal
public import ReasLib.CategoryTheory.Sites.Topos.Morphism

/-!
# Inverse image of ring-valued sheaves along a morphism of topoi

The inverse image of a morphism of topoi is left exact, hence preserves finite products.  It
therefore acts canonically on internal rings.  Converting between ring-valued sheaves and
internal rings gives a presentation-independent inverse-image functor on ring-valued sheaves.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u₀ v₀ u₁ v₁ u₂ v₂ w

namespace CategoryTheory.MorphismOfTopoiIn

open Sheaf.InternalRing

variable {C₀ : Type u₀} [Category.{v₀} C₀]
variable {C₁ : Type u₁} [Category.{v₁} C₁]
variable {C₂ : Type u₂} [Category.{v₂} C₂]
variable {J₀ : GrothendieckTopology C₀} {J₁ : GrothendieckTopology C₁}
variable {J₂ : GrothendieckTopology C₂}

/-- The inverse-image functor on internal rings induced canonically by the left-exact inverse
image of a morphism of topoi.  The canonical braidings are supplied explicitly, so callers do
not need a local instance. -/
noncomputable def internalRingInverseImage
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁) :
    RingObjects J₀ ⥤ RingObjects J₁ :=
  @Functor.mapRingOfFiniteProducts
    (Sheaf J₀ (Type w)) _ _ (sheafBraidedCategory J₀)
    (Sheaf J₁ (Type w)) _ _ (sheafBraidedCategory J₁)
    f.inverseImage inferInstance

/-- Forgetting an internal ring after inverse image recovers inverse image of its underlying
type-valued sheaf. -/
noncomputable def internalRingInverseImageForgetIso
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁) :
    f.internalRingInverseImage ⋙ RingObjects.forget J₁ ≅
      RingObjects.forget J₀ ⋙ f.inverseImage :=
  @Functor.mapRingOfFiniteProductsForgetIso
    (Sheaf J₀ (Type w)) _ _ (sheafBraidedCategory J₀)
    (Sheaf J₁ (Type w)) _ _ (sheafBraidedCategory J₁)
    f.inverseImage inferInstance

/-- A natural transformation between inverse-image functors lifts canonically to internal
rings. -/
noncomputable def internalRingInverseImageNatTrans
    {f g : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁}
    (α : f.inverseImage ⟶ g.inverseImage) :
    f.internalRingInverseImage ⟶ g.internalRingInverseImage :=
  @Functor.mapRingOfFiniteProductsNatTrans
    (Sheaf J₀ (Type w)) _ _ (sheafBraidedCategory J₀)
    (Sheaf J₁ (Type w)) _ _ (sheafBraidedCategory J₁)
    _ _ _ _ α

/-- A natural isomorphism between inverse-image functors lifts canonically to internal
rings. -/
noncomputable def internalRingInverseImageNatIso
    {f g : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁}
    (e : f.inverseImage ≅ g.inverseImage) :
    f.internalRingInverseImage ≅ g.internalRingInverseImage :=
  @Functor.mapRingOfFiniteProductsNatIso
    (Sheaf J₀ (Type w)) _ _ (sheafBraidedCategory J₀)
    (Sheaf J₁ (Type w)) _ _ (sheafBraidedCategory J₁)
    _ _ _ _ e

/-- Internal-ring inverse image along the identity morphism of a topos is naturally isomorphic
to the identity functor. -/
noncomputable def internalRingInverseImageIdIso :
    (MorphismOfTopoiIn.id J₀ :
      MorphismOfTopoiIn.{u₀, u₀, v₀, v₀, w} J₀ J₀).internalRingInverseImage ≅
        𝟭 (RingObjects J₀) :=
  @Functor.mapRingOfFiniteProductsNatIso
      (Sheaf J₀ (Type w)) _ _ (sheafBraidedCategory J₀)
      (Sheaf J₀ (Type w)) _ _ (sheafBraidedCategory J₀)
      _ _ _ _ LeftExactAdjunction.idInverseImageIso ≪≫
    @Functor.mapRingOfFiniteProductsIdIso
      (Sheaf J₀ (Type w)) _ _ (sheafBraidedCategory J₀)

/-- Internal-ring inverse image along a composite is naturally isomorphic to successive
internal-ring inverse image. -/
noncomputable def internalRingInverseImageCompIso
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)
    (g : MorphismOfTopoiIn.{u₁, u₂, v₁, v₂, w} J₁ J₂) :
    (MorphismOfTopoiIn.comp f g).internalRingInverseImage ≅
      f.internalRingInverseImage ⋙ g.internalRingInverseImage :=
  @Functor.mapRingOfFiniteProductsNatIso
      (Sheaf J₀ (Type w)) _ _ (sheafBraidedCategory J₀)
      (Sheaf J₂ (Type w)) _ _ (sheafBraidedCategory J₂)
      _ _ _ _ (LeftExactAdjunction.compInverseImageIso f g) ≪≫
    @Functor.mapRingOfFiniteProductsCompIso
      (Sheaf J₀ (Type w)) _ _ (sheafBraidedCategory J₀)
      (Sheaf J₁ (Type w)) _ _ (sheafBraidedCategory J₁)
      (Sheaf J₂ (Type w)) _ _ (sheafBraidedCategory J₂)
      f.inverseImage _ g.inverseImage _

/-- The direct-image functor on internal rings induced canonically by the right adjoint of a
morphism of topoi. -/
noncomputable def internalRingDirectImage
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁) :
    RingObjects J₁ ⥤ RingObjects J₀ :=
  @Functor.mapRingOfFiniteProducts
    (Sheaf J₁ (Type w)) _ _ (sheafBraidedCategory J₁)
    (Sheaf J₀ (Type w)) _ _ (sheafBraidedCategory J₀)
    f.pushforward (LeftExactAdjunction.pushforwardPreservesFiniteProducts f)

/-- Forgetting an internal ring after direct image recovers direct image of its underlying
type-valued sheaf. -/
noncomputable def internalRingDirectImageForgetIso
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁) :
    f.internalRingDirectImage ⋙ RingObjects.forget J₀ ≅
      RingObjects.forget J₁ ⋙ f.pushforward :=
  @Functor.mapRingOfFiniteProductsForgetIso
    (Sheaf J₁ (Type w)) _ _ (sheafBraidedCategory J₁)
    (Sheaf J₀ (Type w)) _ _ (sheafBraidedCategory J₀)
    f.pushforward (LeftExactAdjunction.pushforwardPreservesFiniteProducts f)

/-- A natural transformation between direct-image functors lifts canonically to internal
rings. -/
noncomputable def internalRingDirectImageNatTrans
    {f g : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁}
    (α : f.pushforward ⟶ g.pushforward) :
    f.internalRingDirectImage ⟶ g.internalRingDirectImage :=
  @Functor.mapRingOfFiniteProductsNatTrans
    (Sheaf J₁ (Type w)) _ _ (sheafBraidedCategory J₁)
    (Sheaf J₀ (Type w)) _ _ (sheafBraidedCategory J₀)
    _ _ (LeftExactAdjunction.pushforwardPreservesFiniteProducts f)
      (LeftExactAdjunction.pushforwardPreservesFiniteProducts g) α

/-- A natural isomorphism between direct-image functors lifts canonically to internal rings. -/
noncomputable def internalRingDirectImageNatIso
    {f g : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁}
    (e : f.pushforward ≅ g.pushforward) :
    f.internalRingDirectImage ≅ g.internalRingDirectImage :=
  @Functor.mapRingOfFiniteProductsNatIso
    (Sheaf J₁ (Type w)) _ _ (sheafBraidedCategory J₁)
    (Sheaf J₀ (Type w)) _ _ (sheafBraidedCategory J₀)
    _ _ (LeftExactAdjunction.pushforwardPreservesFiniteProducts f)
      (LeftExactAdjunction.pushforwardPreservesFiniteProducts g) e

/-- Lifting the identity direct-image transformation gives the identity on internal rings. -/
@[simp]
theorem internalRingDirectImageNatTrans_id
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁) :
    internalRingDirectImageNatTrans (𝟙 f.pushforward) =
      𝟙 f.internalRingDirectImage := sorry

/-- Lifting direct-image transformations preserves vertical composition. -/
@[simp]
theorem internalRingDirectImageNatTrans_comp
    {f g h : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁}
    (α : f.pushforward ⟶ g.pushforward)
    (β : g.pushforward ⟶ h.pushforward) :
    internalRingDirectImageNatTrans (α ≫ β) =
      internalRingDirectImageNatTrans α ≫
        internalRingDirectImageNatTrans β := sorry

/-- Forgetting the lifted direct-image transformation gives the original transformation on
underlying sheaves. -/
theorem internalRingDirectImageNatTrans_forget
    {f g : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁}
    (α : f.pushforward ⟶ g.pushforward) (R : RingObjects J₁) :
    f.internalRingDirectImageForgetIso.hom.app R ≫
        α.app ((RingObjects.forget J₁).obj R) =
      (RingObjects.forget J₀).map
          ((internalRingDirectImageNatTrans α).app R) ≫
        g.internalRingDirectImageForgetIso.hom.app R := sorry

/-- The canonical inverse- and direct-image functors on internal rings form an adjunction. -/
noncomputable def internalRingAdjunction
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁) :
    f.internalRingInverseImage ⊣ f.internalRingDirectImage :=
  @Functor.mapRingOfFiniteProductsAdjunction
    (Sheaf J₀ (Type w)) _ _ (sheafBraidedCategory J₀)
    (Sheaf J₁ (Type w)) _ _ (sheafBraidedCategory J₁)
    f.inverseImage _ f.pushforward
      (LeftExactAdjunction.pushforwardPreservesFiniteProducts f) f.adjunction

/-- The canonical inverse-image functor on ring-valued sheaves along a morphism of topoi.
It is obtained without choosing a site functor: pass to internal rings, apply the left-exact
inverse image, and reconstruct the ring-valued sheaf. -/
noncomputable def ringInverseImage
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)
    [J₀.HasSheafCompose (forget RingCat.{w})]
    [J₁.HasSheafCompose (forget RingCat.{w})] :
    Sheaf J₀ RingCat.{w} ⥤ Sheaf J₁ RingCat.{w} :=
  toInternal ⋙ f.internalRingInverseImage ⋙ fromInternal

/-- A natural transformation between inverse images lifts canonically to ring-valued
sheaves. -/
@[stacks 08PA "ring inverse-image comparison lift"]
noncomputable def ringInverseImageNatTrans
    {f g : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁}
    [J₀.HasSheafCompose (forget RingCat.{w})]
    [J₁.HasSheafCompose (forget RingCat.{w})]
    (α : f.inverseImage ⟶ g.inverseImage) :
    f.ringInverseImage ⟶ g.ringInverseImage :=
  Functor.whiskerLeft toInternal
    (Functor.whiskerRight (internalRingInverseImageNatTrans α) fromInternal)

/-- A natural isomorphism between inverse images lifts canonically to ring-valued
sheaves. -/
@[stacks 08PA "ring inverse-image isomorphism lift"]
noncomputable def ringInverseImageNatIso
    {f g : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁}
    [J₀.HasSheafCompose (forget RingCat.{w})]
    [J₁.HasSheafCompose (forget RingCat.{w})]
    (e : f.inverseImage ≅ g.inverseImage) :
    f.ringInverseImage ≅ g.ringInverseImage :=
  Functor.isoWhiskerLeft toInternal
    (Functor.isoWhiskerRight (internalRingInverseImageNatIso e) fromInternal)

/-- The canonical direct-image functor on ring-valued sheaves along a morphism of topoi. -/
noncomputable def ringDirectImage
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)
    [J₀.HasSheafCompose (forget RingCat.{w})]
    [J₁.HasSheafCompose (forget RingCat.{w})] :
    Sheaf J₁ RingCat.{w} ⥤ Sheaf J₀ RingCat.{w} :=
  toInternal ⋙ f.internalRingDirectImage ⋙ fromInternal

/-- A natural transformation between direct-image functors lifts canonically to ring-valued
sheaves. -/
noncomputable def ringDirectImageNatTrans
    {f g : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁}
    [J₀.HasSheafCompose (forget RingCat.{w})]
    [J₁.HasSheafCompose (forget RingCat.{w})]
    (α : f.pushforward ⟶ g.pushforward) :
    f.ringDirectImage ⟶ g.ringDirectImage :=
  Functor.whiskerLeft toInternal
    (Functor.whiskerRight (internalRingDirectImageNatTrans α) fromInternal)

/-- A natural isomorphism between direct-image functors lifts canonically to ring-valued
sheaves. -/
noncomputable def ringDirectImageNatIso
    {f g : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁}
    [J₀.HasSheafCompose (forget RingCat.{w})]
    [J₁.HasSheafCompose (forget RingCat.{w})]
    (e : f.pushforward ≅ g.pushforward) :
    f.ringDirectImage ≅ g.ringDirectImage :=
  Functor.isoWhiskerLeft toInternal
    (Functor.isoWhiskerRight (internalRingDirectImageNatIso e) fromInternal)

/-- Lifting the identity direct-image transformation gives the identity on ring-valued
sheaves. -/
@[simp]
theorem ringDirectImageNatTrans_id
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)
    [J₀.HasSheafCompose (forget RingCat.{w})]
    [J₁.HasSheafCompose (forget RingCat.{w})] :
    ringDirectImageNatTrans (𝟙 f.pushforward) =
      𝟙 f.ringDirectImage := sorry

/-- Lifting direct-image transformations to ring-valued sheaves preserves vertical
composition. -/
@[simp]
theorem ringDirectImageNatTrans_comp
    {f g h : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁}
    [J₀.HasSheafCompose (forget RingCat.{w})]
    [J₁.HasSheafCompose (forget RingCat.{w})]
    (α : f.pushforward ⟶ g.pushforward)
    (β : g.pushforward ⟶ h.pushforward) :
    ringDirectImageNatTrans (α ≫ β) =
      ringDirectImageNatTrans α ≫ ringDirectImageNatTrans β := sorry

/-- The forward transformation of the lifted direct-image isomorphism is the lift of its
forward transformation. -/
@[simp]
theorem ringDirectImageNatIso_hom
    {f g : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁}
    [J₀.HasSheafCompose (forget RingCat.{w})]
    [J₁.HasSheafCompose (forget RingCat.{w})]
    (e : f.pushforward ≅ g.pushforward) :
    (ringDirectImageNatIso e).hom = ringDirectImageNatTrans e.hom := sorry

/-- The inverse transformation of the lifted direct-image isomorphism is the lift of its
inverse transformation. -/
@[simp]
theorem ringDirectImageNatIso_inv
    {f g : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁}
    [J₀.HasSheafCompose (forget RingCat.{w})]
    [J₁.HasSheafCompose (forget RingCat.{w})]
    (e : f.pushforward ≅ g.pushforward) :
    (ringDirectImageNatIso e).inv = ringDirectImageNatTrans e.inv := sorry

/-- Canonical inverse and direct image on ring-valued sheaves form an adjunction. -/
noncomputable def ringAdjunction
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)
    [J₀.HasSheafCompose (forget RingCat.{w})]
    [J₁.HasSheafCompose (forget RingCat.{w})] :
    f.ringInverseImage ⊣ f.ringDirectImage :=
  ((equivalence (J := J₀)).toAdjunction.comp f.internalRingAdjunction).comp
    (equivalence (J := J₁)).symm.toAdjunction

/-- Canonical inverse image of ring-valued sheaves along the identity morphism of a topos is
naturally isomorphic to the identity functor. -/
noncomputable def ringInverseImageIdIso
    [J₀.HasSheafCompose (forget RingCat.{w})] :
    (MorphismOfTopoiIn.id J₀ :
      MorphismOfTopoiIn.{u₀, u₀, v₀, v₀, w} J₀ J₀).ringInverseImage ≅
        𝟭 (Sheaf J₀ RingCat.{w}) :=
  Functor.isoWhiskerLeft toInternal
      (Functor.isoWhiskerRight
        (internalRingInverseImageIdIso (J₀ := J₀)) fromInternal) ≪≫
    Functor.isoWhiskerLeft toInternal (Functor.leftUnitor fromInternal) ≪≫
    toFromIso

/-- Canonical inverse image of ring-valued sheaves along a composite agrees naturally with
successive inverse image. -/
noncomputable def ringInverseImageCompIso
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)
    (g : MorphismOfTopoiIn.{u₁, u₂, v₁, v₂, w} J₁ J₂)
    [J₀.HasSheafCompose (forget RingCat.{w})]
    [J₁.HasSheafCompose (forget RingCat.{w})]
    [J₂.HasSheafCompose (forget RingCat.{w})] :
    (MorphismOfTopoiIn.comp f g).ringInverseImage ≅
      f.ringInverseImage ⋙ g.ringInverseImage :=
  Functor.isoWhiskerLeft toInternal
      (Functor.isoWhiskerRight (internalRingInverseImageCompIso f g) fromInternal) ≪≫
    Functor.isoWhiskerLeft toInternal
      (Functor.associator f.internalRingInverseImage
        g.internalRingInverseImage fromInternal) ≪≫
    Functor.isoWhiskerLeft toInternal
      (Functor.isoWhiskerLeft f.internalRingInverseImage
        (Functor.leftUnitor (g.internalRingInverseImage ⋙ fromInternal)).symm) ≪≫
    Functor.isoWhiskerLeft toInternal
      (Functor.isoWhiskerLeft f.internalRingInverseImage
        (Functor.isoWhiskerRight fromToIso.symm
          (g.internalRingInverseImage ⋙ fromInternal))) ≪≫
    Functor.isoWhiskerLeft toInternal
      (Functor.isoWhiskerLeft f.internalRingInverseImage
        (Functor.associator fromInternal toInternal
          (g.internalRingInverseImage ⋙ fromInternal))) ≪≫
    Functor.isoWhiskerLeft toInternal
      (Functor.associator f.internalRingInverseImage fromInternal
        (toInternal ⋙ g.internalRingInverseImage ⋙ fromInternal)).symm ≪≫
    (Functor.associator
      toInternal (f.internalRingInverseImage ⋙ fromInternal)
      (toInternal ⋙ g.internalRingInverseImage ⋙ fromInternal)).symm

/-- Forgetting ring structure after the canonical ring inverse image recovers the underlying
type-valued inverse image. -/
noncomputable def ringInverseImageForgetIso
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)
    [J₀.HasSheafCompose (forget RingCat.{w})]
    [J₁.HasSheafCompose (forget RingCat.{w})] :
    f.ringInverseImage ⋙ sheafCompose J₁ (forget RingCat.{w}) ≅
      sheafCompose J₀ (forget RingCat.{w}) ⋙ f.inverseImage :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (toInternal ⋙ f.internalRingInverseImage)
      fromInternalForgetIso ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft toInternal f.internalRingInverseImageForgetIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight toInternalForgetIso f.inverseImage

/-- Forgetting ring structure after canonical ring direct image recovers the underlying
type-valued direct image. -/
noncomputable def ringDirectImageForgetIso
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)
    [J₀.HasSheafCompose (forget RingCat.{w})]
    [J₁.HasSheafCompose (forget RingCat.{w})] :
    f.ringDirectImage ⋙ sheafCompose J₀ (forget RingCat.{w}) ≅
      sheafCompose J₁ (forget RingCat.{w}) ⋙ f.pushforward :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (toInternal ⋙ f.internalRingDirectImage)
      fromInternalForgetIso ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft toInternal f.internalRingDirectImageForgetIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight toInternalForgetIso f.pushforward

/-- Forgetting the ring-valued lift of a direct-image transformation gives the original
transformation on underlying sheaves. -/
theorem ringDirectImageNatTrans_forget
    {f g : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁}
    [J₀.HasSheafCompose (forget RingCat.{w})]
    [J₁.HasSheafCompose (forget RingCat.{w})]
    (α : f.pushforward ⟶ g.pushforward) (R : Sheaf J₁ RingCat.{w}) :
    f.ringDirectImageForgetIso.hom.app R ≫
        α.app ((sheafCompose J₁ (forget RingCat.{w})).obj R) =
      (sheafCompose J₀ (forget RingCat.{w})).map
          ((ringDirectImageNatTrans α).app R) ≫
        g.ringDirectImageForgetIso.hom.app R := sorry

-- The carrier functor and every ring operation are inherited from the explicit internal-ring
-- conversions and `mapRingOfFiniteProducts`; no inverse is selected from an `IsIso` proof.

end CategoryTheory.MorphismOfTopoiIn
