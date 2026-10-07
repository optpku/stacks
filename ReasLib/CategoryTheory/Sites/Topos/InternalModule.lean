module

public import ReasLib.Algebra.Category.Module.Internal.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Internal
public import ReasLib.CategoryTheory.Sites.Topos.InternalRing
import Mathlib.Tactic.CrossRefAttribute

/-!
# Inverse and direct image of module sheaves along a morphism of topoi

The inverse image of a morphism of topoi preserves finite products, so it carries internal
modules to internal modules over the inverse-image internal ring.  The reconstruction
comparison for internal rings then transports these modules to modules over the canonical
ring-valued inverse image.  This gives a presentation-independent inverse-image functor on
sheaves of modules.  Applying the finite-product-preserving right adjoint gives the symmetric
direct-image construction over the canonical ring-valued direct image.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u₀ v₀ u₁ v₁ u₂ v₂ w

namespace CategoryTheory.Sheaf.InternalModule

variable {C : Type u₀} [Category.{v₀} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget RingCat.{w})]

/-- Forgetting after reconstructing an internal module recovers its underlying type-valued
sheaf. -/
noncomputable def fromInternalUnderlyingIso (R : Sheaf J RingCat.{w}) :
    fromInternal R ⋙ ToInternal.underlying R ≅ ModuleObjects.forget R :=
  (Functor.isoWhiskerLeft (fromInternal R) (toInternalForgetIso R)).symm ≪≫
    (Functor.associator (fromInternal R) (toInternal R)
      (ModuleObjects.forget R)).symm ≪≫
    Functor.isoWhiskerRight (fromToIso R) (ModuleObjects.forget R) ≪≫
    Functor.leftUnitor (ModuleObjects.forget R)

end CategoryTheory.Sheaf.InternalModule

namespace CategoryTheory.MorphismOfTopoiIn

open Sheaf.InternalModule Sheaf.InternalRing

variable {C₀ : Type u₀} [Category.{v₀} C₀]
variable {C₁ : Type u₁} [Category.{v₁} C₁]
variable {J₀ : GrothendieckTopology C₀} {J₁ : GrothendieckTopology C₁}

/-- The inverse image of internal modules induced by the finite-product-preserving inverse
image of a morphism of topoi. -/
@[stacks 03D6 "inverse image of internal modules"]
noncomputable def internalModuleInverseImage
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)
    (R : RingObjects.{u₀, v₀, w} J₀) :
    @ModuleObjCat (Sheaf J₀ (Type w)) _ _ (sheafBraidedCategory J₀) R ⥤
      @ModuleObjCat (Sheaf J₁ (Type w)) _ _ (sheafBraidedCategory J₁)
        (f.internalRingInverseImage.obj R) :=
  @Functor.mapModuleOfFiniteProducts
    (Sheaf J₀ (Type w)) _ _ (sheafBraidedCategory J₀)
    (Sheaf J₁ (Type w)) _ _ (sheafBraidedCategory J₁)
    f.inverseImage inferInstance R

/-- Forgetting internal-module structure after inverse image recovers inverse image of the
underlying type-valued sheaf. -/
noncomputable def internalModuleInverseImageForgetIso
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)
    (R : RingObjects.{u₀, v₀, w} J₀) :
    f.internalModuleInverseImage R ⋙
        @ModuleObjCat.forget (Sheaf J₁ (Type w)) _ _ (sheafBraidedCategory J₁)
          (f.internalRingInverseImage.obj R) ≅
      @ModuleObjCat.forget (Sheaf J₀ (Type w)) _ _ (sheafBraidedCategory J₀) R ⋙
        f.inverseImage :=
  @Functor.mapModuleOfFiniteProductsForgetIso
    (Sheaf J₀ (Type w)) _ _ (sheafBraidedCategory J₀)
    (Sheaf J₁ (Type w)) _ _ (sheafBraidedCategory J₁)
    f.inverseImage inferInstance R

/-- The direct image of internal modules induced by the finite-product-preserving direct image
of a morphism of topoi. -/
@[stacks 03D6 "direct image of internal modules"]
noncomputable def internalModuleDirectImage
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)
    (R : RingObjects.{u₁, v₁, w} J₁) :
    @ModuleObjCat (Sheaf J₁ (Type w)) _ _ (sheafBraidedCategory J₁) R ⥤
      @ModuleObjCat (Sheaf J₀ (Type w)) _ _ (sheafBraidedCategory J₀)
        (f.internalRingDirectImage.obj R) :=
  @Functor.mapModuleOfFiniteProducts
    (Sheaf J₁ (Type w)) _ _ (sheafBraidedCategory J₁)
    (Sheaf J₀ (Type w)) _ _ (sheafBraidedCategory J₀)
    f.pushforward (LeftExactAdjunction.pushforwardPreservesFiniteProducts f) R

/-- Forgetting internal-module structure after direct image recovers direct image of the
underlying type-valued sheaf. -/
noncomputable def internalModuleDirectImageForgetIso
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)
    (R : RingObjects.{u₁, v₁, w} J₁) :
    f.internalModuleDirectImage R ⋙
        @ModuleObjCat.forget (Sheaf J₀ (Type w)) _ _ (sheafBraidedCategory J₀)
          (f.internalRingDirectImage.obj R) ≅
      @ModuleObjCat.forget (Sheaf J₁ (Type w)) _ _ (sheafBraidedCategory J₁) R ⋙
        f.pushforward :=
  @Functor.mapModuleOfFiniteProductsForgetIso
    (Sheaf J₁ (Type w)) _ _ (sheafBraidedCategory J₁)
    (Sheaf J₀ (Type w)) _ _ (sheafBraidedCategory J₀)
    f.pushforward (LeftExactAdjunction.pushforwardPreservesFiniteProducts f) R

variable [J₀.HasSheafCompose (forget RingCat.{w})]
variable [J₁.HasSheafCompose (forget RingCat.{w})]

/-- The internal-ring comparison from the internal ring underlying the canonical ring-valued
inverse image to the internal-ring inverse image. -/
@[stacks 03D6 "internal-ring comparison"]
noncomputable def moduleInverseImageRingComparison
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)
    (R : Sheaf J₀ RingCat.{w}) :
    toInternal.obj (f.ringInverseImage.obj R) ⟶
      f.internalRingInverseImage.obj (toInternal.obj R) :=
  fromToIso.hom.app (f.internalRingInverseImage.obj (toInternal.obj R))

/-- The internal-ring comparison used in module inverse image is an isomorphism. -/
noncomputable instance moduleInverseImageRingComparison_isIso
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)
    (R : Sheaf J₀ RingCat.{w}) :
    IsIso (f.moduleInverseImageRingComparison R) :=
  (fromToIso.app (f.internalRingInverseImage.obj (toInternal.obj R))).isIso_hom

/-- The canonical isomorphism underlying the internal-ring comparison used in module inverse
image. -/
noncomputable def moduleInverseImageRingIso
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)
    (R : Sheaf J₀ RingCat.{w}) :
    toInternal.obj (f.ringInverseImage.obj R) ≅
      f.internalRingInverseImage.obj (toInternal.obj R) :=
  fromToIso.app (f.internalRingInverseImage.obj (toInternal.obj R))

/-- The forward map of the internal-ring comparison is the comparison morphism used by module
inverse image. -/
@[simp]
theorem moduleInverseImageRingIso_hom
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)
    (R : Sheaf J₀ RingCat.{w}) :
    (f.moduleInverseImageRingIso R).hom = f.moduleInverseImageRingComparison R := sorry

/-- The internal-ring comparison used by module inverse image is natural in the coefficient
ring sheaf. -/
theorem moduleInverseImageRingComparison_naturality
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)
    {R S : Sheaf J₀ RingCat.{w}} (α : R ⟶ S) :
    toInternal.map (f.ringInverseImage.map α) ≫
        f.moduleInverseImageRingComparison S =
      f.moduleInverseImageRingComparison R ≫
        f.internalRingInverseImage.map (toInternal.map α) := sorry

/-- The internal-ring comparison for the identity morphism is compatible with the identity
comparisons for ring-valued and internal-ring inverse image. -/
theorem moduleInverseImageRingComparison_id (R : Sheaf J₀ RingCat.{w}) :
    ((MorphismOfTopoiIn.id J₀ :
        MorphismOfTopoiIn.{u₀, u₀, v₀, v₀, w} J₀ J₀).moduleInverseImageRingComparison R) ≫
        (internalRingInverseImageIdIso (J₀ := J₀)).hom.app (toInternal.obj R) =
      toInternal.map ((ringInverseImageIdIso (J₀ := J₀)).hom.app R) := sorry

/-- The internal-ring comparison for a composite morphism agrees with the successive
comparisons for its two factors. -/
theorem moduleInverseImageRingComparison_comp
    {C₂ : Type u₂} [Category.{v₂} C₂] {J₂ : GrothendieckTopology C₂}
    [J₂.HasSheafCompose (forget RingCat.{w})]
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)
    (g : MorphismOfTopoiIn.{u₁, u₂, v₁, v₂, w} J₁ J₂)
    (R : Sheaf J₀ RingCat.{w}) :
    (MorphismOfTopoiIn.comp f g).moduleInverseImageRingComparison R ≫
        (internalRingInverseImageCompIso f g).hom.app (toInternal.obj R) =
      toInternal.map ((ringInverseImageCompIso f g).hom.app R) ≫
        g.moduleInverseImageRingComparison (f.ringInverseImage.obj R) ≫
          g.internalRingInverseImage.map (f.moduleInverseImageRingComparison R) := sorry

/-- The presentation-independent inverse image of sheaves of modules along a morphism of
topoi. -/
@[stacks 03D6 "presentation-independent module inverse image"]
noncomputable def moduleInverseImage
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)
    (R : Sheaf J₀ RingCat.{w}) :
    SheafOfModules.{w} R ⥤ SheafOfModules.{w} (f.ringInverseImage.obj R) :=
  Sheaf.InternalModule.toInternal R ⋙
    f.internalModuleInverseImage (toInternal.obj R) ⋙
    @ModuleObjCat.restrictScalars (Sheaf J₁ (Type w)) _ _
      (sheafBraidedCategory J₁) _ _ (f.moduleInverseImageRingComparison R) ⋙
    Sheaf.InternalModule.fromInternal (f.ringInverseImage.obj R)

/-- Forgetting module structure after the presentation-independent module inverse image
recovers inverse image of the underlying type-valued sheaf. -/
@[stacks 03D6 "underlying sheaf of module inverse image"]
noncomputable def moduleInverseImageForgetIso
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)
    (R : Sheaf J₀ RingCat.{w}) :
    f.moduleInverseImage R ⋙
        Sheaf.InternalModule.ToInternal.underlying (f.ringInverseImage.obj R) ≅
      Sheaf.InternalModule.ToInternal.underlying R ⋙ f.inverseImage :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (Sheaf.InternalModule.toInternal R ⋙
        f.internalModuleInverseImage (toInternal.obj R) ⋙
        @ModuleObjCat.restrictScalars (Sheaf J₁ (Type w)) _ _
          (sheafBraidedCategory J₁) _ _ (f.moduleInverseImageRingComparison R))
      (Sheaf.InternalModule.fromInternalUnderlyingIso
        (f.ringInverseImage.obj R)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (Sheaf.InternalModule.toInternal R ⋙
        f.internalModuleInverseImage (toInternal.obj R))
      (@ModuleObjCat.restrictScalarsForgetIso (Sheaf J₁ (Type w)) _ _
        (sheafBraidedCategory J₁) _ _ (f.moduleInverseImageRingComparison R)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Sheaf.InternalModule.toInternal R)
      (f.internalModuleInverseImageForgetIso (toInternal.obj R)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Sheaf.InternalModule.toInternalForgetIso R) f.inverseImage

/-- The underlying-sheaf comparison for module inverse image is natural in a module
morphism. -/
theorem moduleInverseImageForgetIso_naturality
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)
    (R : Sheaf J₀ RingCat.{w}) {M N : SheafOfModules.{w} R} (g : M ⟶ N) :
    (Sheaf.InternalModule.ToInternal.underlying (f.ringInverseImage.obj R)).map
          ((f.moduleInverseImage R).map g) ≫
        (f.moduleInverseImageForgetIso R).hom.app N =
      (f.moduleInverseImageForgetIso R).hom.app M ≫
        f.inverseImage.map ((Sheaf.InternalModule.ToInternal.underlying R).map g) := sorry

/-- The internal-ring comparison from the internal ring underlying the canonical ring-valued
direct image to the internal-ring direct image. -/
@[stacks 03D6 "direct-image internal-ring comparison"]
noncomputable def moduleDirectImageRingComparison
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)
    (R : Sheaf J₁ RingCat.{w}) :
    toInternal.obj (f.ringDirectImage.obj R) ⟶
      f.internalRingDirectImage.obj (toInternal.obj R) :=
  fromToIso.hom.app (f.internalRingDirectImage.obj (toInternal.obj R))

/-- The internal-ring comparison used in module direct image is an isomorphism. -/
noncomputable instance moduleDirectImageRingComparison_isIso
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)
    (R : Sheaf J₁ RingCat.{w}) :
    IsIso (f.moduleDirectImageRingComparison R) :=
  (fromToIso.app (f.internalRingDirectImage.obj (toInternal.obj R))).isIso_hom

/-- The canonical isomorphism underlying the internal-ring comparison used in module direct
image. -/
noncomputable def moduleDirectImageRingIso
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)
    (R : Sheaf J₁ RingCat.{w}) :
    toInternal.obj (f.ringDirectImage.obj R) ≅
      f.internalRingDirectImage.obj (toInternal.obj R) :=
  fromToIso.app (f.internalRingDirectImage.obj (toInternal.obj R))

/-- The forward map of the direct-image internal-ring comparison is its comparison
morphism. -/
@[simp]
theorem moduleDirectImageRingIso_hom
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)
    (R : Sheaf J₁ RingCat.{w}) :
    (f.moduleDirectImageRingIso R).hom = f.moduleDirectImageRingComparison R := sorry

/-- The internal-ring comparison used by module direct image is natural in the coefficient
ring sheaf. -/
theorem moduleDirectImageRingComparison_naturality
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)
    {R S : Sheaf J₁ RingCat.{w}} (α : R ⟶ S) :
    toInternal.map (f.ringDirectImage.map α) ≫
        f.moduleDirectImageRingComparison S =
      f.moduleDirectImageRingComparison R ≫
        f.internalRingDirectImage.map (toInternal.map α) := sorry

/-- The presentation-independent direct image of sheaves of modules along a morphism of
topoi. -/
@[stacks 03D6 "presentation-independent module direct image"]
noncomputable def moduleDirectImage
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)
    (R : Sheaf J₁ RingCat.{w}) :
    SheafOfModules.{w} R ⥤ SheafOfModules.{w} (f.ringDirectImage.obj R) :=
  Sheaf.InternalModule.toInternal R ⋙
    f.internalModuleDirectImage (toInternal.obj R) ⋙
    @ModuleObjCat.restrictScalars (Sheaf J₀ (Type w)) _ _
      (sheafBraidedCategory J₀) _ _ (f.moduleDirectImageRingComparison R) ⋙
    Sheaf.InternalModule.fromInternal (f.ringDirectImage.obj R)

/-- Forgetting module structure after the presentation-independent module direct image
recovers direct image of the underlying type-valued sheaf. -/
@[stacks 03D6 "underlying sheaf of module direct image"]
noncomputable def moduleDirectImageForgetIso
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)
    (R : Sheaf J₁ RingCat.{w}) :
    f.moduleDirectImage R ⋙
        Sheaf.InternalModule.ToInternal.underlying (f.ringDirectImage.obj R) ≅
      Sheaf.InternalModule.ToInternal.underlying R ⋙ f.pushforward :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (Sheaf.InternalModule.toInternal R ⋙
        f.internalModuleDirectImage (toInternal.obj R) ⋙
        @ModuleObjCat.restrictScalars (Sheaf J₀ (Type w)) _ _
          (sheafBraidedCategory J₀) _ _ (f.moduleDirectImageRingComparison R))
      (Sheaf.InternalModule.fromInternalUnderlyingIso
        (f.ringDirectImage.obj R)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (Sheaf.InternalModule.toInternal R ⋙
        f.internalModuleDirectImage (toInternal.obj R))
      (@ModuleObjCat.restrictScalarsForgetIso (Sheaf J₀ (Type w)) _ _
        (sheafBraidedCategory J₀) _ _ (f.moduleDirectImageRingComparison R)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Sheaf.InternalModule.toInternal R)
      (f.internalModuleDirectImageForgetIso (toInternal.obj R)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Sheaf.InternalModule.toInternalForgetIso R) f.pushforward

/-- The underlying-sheaf comparison for module direct image is natural in a module
morphism. -/
theorem moduleDirectImageForgetIso_naturality
    (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)
    (R : Sheaf J₁ RingCat.{w}) {M N : SheafOfModules.{w} R} (g : M ⟶ N) :
    (Sheaf.InternalModule.ToInternal.underlying (f.ringDirectImage.obj R)).map
          ((f.moduleDirectImage R).map g) ≫
        (f.moduleDirectImageForgetIso R).hom.app N =
      (f.moduleDirectImageForgetIso R).hom.app M ≫
        f.pushforward.map ((Sheaf.InternalModule.ToInternal.underlying R).map g) := sorry

end CategoryTheory.MorphismOfTopoiIn
