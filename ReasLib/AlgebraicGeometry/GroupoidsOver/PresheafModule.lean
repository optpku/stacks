/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Bottom
public import ReasLib.AlgebraicGeometry.GroupoidsOver.StructureSheaf
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.CategoryTheory.Sites.Chaotic
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.CategoryTheory.Sites.Topos.InternalModule

/-!
# Functoriality of presheaves of modules on categories fibred in groupoids

Inverse image is precomposition with canonical restriction of scalars. Direct image is
constructed on the bottom sites from the geometric direct image and the adjunct of the
structure-presheaf identification.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor Opposite
open FiberedCategoryOver.Groupoids

noncomputable section

universe u z

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The structure sheaf `𝒪_X`, rebundled as a sheaf for the chaotic topology on
the total category of `X`. -/
def chaoticStructureSheaf (X : GroupoidsOver S) :
    Sheaf (⊥ : GrothendieckTopology X.total) RingCat.{u} :=
  ⟨(structureSheaf X).obj, Presheaf.isSheaf_bot _⟩

/-- The underlying ring presheaf of `chaoticStructureSheaf X` is `𝒪_X`. -/
theorem chaoticStructureSheaf_obj (X : GroupoidsOver S) :
    (chaoticStructureSheaf X).obj = (structureSheaf X).obj := sorry

/-- Unfolding of `𝒪_X = p⁻¹ 𝒪` as precomposition with `X.p.op`. -/
def structureSheafToBig (X : GroupoidsOver S) :
    (structureSheaf X).obj ≅
      X.p.op ⋙ (StandardTopology.Big.structureSheaf .fppf S).obj :=
  (X.p.sheafPushforwardContinuousCompSheafToPresheafIso RingCat.{u}
      (fppfTopology X) (Scheme.fppfTopology.over S)).app
    (StandardTopology.Big.structureSheaf .fppf S)

/-- The identification `f⁻¹ 𝒪_Y = 𝒪_X` of ring presheaves, from the commuting
triangle `toFunctor f ⋙ Y.p = X.p` and the definition `𝒪 = p⁻¹ 𝒪`. -/
def structureSheafInverseImageIso {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (toFunctor f).op ⋙ (structureSheaf Y).obj ≅ (structureSheaf X).obj :=
  isoWhiskerLeft (toFunctor f).op (structureSheafToBig Y) ≪≫
    isoWhiskerRight ((toFunctor f).opComp Y.p).symm
      (StandardTopology.Big.structureSheaf .fppf S).obj ≪≫
    isoWhiskerRight (NatIso.op (commIso f).symm)
      (StandardTopology.Big.structureSheaf .fppf S).obj ≪≫
    (structureSheafToBig X).symm

/-- The coefficient rings at an object and its image under a morphism of categories
fibred in groupoids are equal. -/
theorem structureSheafInverseImageIso_hom_app {X Y : GroupoidsOver S}
    (f : X ⟶ Y) (x : X.total) :
    ((toFunctor f).op ⋙ (structureSheaf Y).obj).obj (op x) =
      (structureSheaf X).obj.obj (op x) := sorry

/-- Inverse image of presheaves of modules along a 1-morphism
`f : X ⟶ Y`, obtained by precomposition and canonical restriction of scalars. -/
abbrev presheafModuleInverseImage {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    PresheafOfModules.{z} (structureSheaf Y).obj ⥤
      PresheafOfModules.{z} (structureSheaf X).obj :=
  PresheafOfModules.pushforward.{z} (structureSheafInverseImageIso f).inv

/-- Inverse image of presheaves of modules commutes with the forgetful functor
to abelian presheaves, and is precomposition with `(toFunctor f).op`. -/
def presheafModuleInverseImage_toPresheaf {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    presheafModuleInverseImage f ⋙
        PresheafOfModules.toPresheaf (structureSheaf X).obj ≅
      PresheafOfModules.toPresheaf (structureSheaf Y).obj ⋙
        (whiskeringLeft _ _ _).obj (toFunctor f).op :=
  PresheafOfModules.pushforwardCompToPresheaf (structureSheafInverseImageIso f).inv

/-- The inverse image of a presheaf of modules evaluates at `x` as the original
module at `f(x)`, with scalars restricted along `𝒪_Y(f(x)) = 𝒪_X(x)`. -/
theorem presheafModuleInverseImage_obj {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (𝒢 : PresheafOfModules.{z} (structureSheaf Y).obj) (x : X.total) :
    ((presheafModuleInverseImage f).obj 𝒢).obj (op x) =
      (ModuleCat.restrictScalars
          ((structureSheafInverseImageIso f).inv.app (op x)).hom).obj
        ((PresheafOfModules.pushforward₀Obj (toFunctor f) (structureSheaf Y).obj 𝒢).obj
          (op x)) := sorry

open CategoryTheory.Sheaf.InternalRing

variable {X Y : GroupoidsOver S} (f : X ⟶ Y)
variable [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]

/-- A morphism of categories fibred in groupoids induces a geometric morphism on the
bottom sites. -/
def chaoticToposHom :
    MorphismOfTopoiIn (⊥ : GrothendieckTopology Y.total)
      (⊥ : GrothendieckTopology X.total) :=
  (toFunctor f).morphismOfTopoiInOfCocontinuous ⊥ ⊥

/-- The structure-presheaf identification induces the underlying-type inverse-image
structure map by the sheafification adjunction. -/
def chaoticInverseImageStructureMap :
    (chaoticToposHom f).inverseImage.obj (underlying.{u + 1, u, u} (chaoticStructureSheaf Y)) ⟶
      underlying.{u + 1, u, u} (chaoticStructureSheaf X) :=
  ((sheafificationAdjunction (⊥ : GrothendieckTopology X.total) (Type u)).homEquiv
    _ _).symm
    (Functor.whiskerRight (structureSheafInverseImageIso f).hom (forget RingCat.{u}))

/-- The adjunct of the inverse-image structure map, transported to the carriers of the
canonical internal structure rings. -/
def chaoticDirectStructureMapUnderlying :
    RingObjects.carrier (⊥ : GrothendieckTopology Y.total)
        (toInternal.{u + 1, u, u}.obj (chaoticStructureSheaf Y)) ⟶
      RingObjects.carrier (⊥ : GrothendieckTopology Y.total)
        ((chaoticToposHom f).internalRingDirectImage.obj
          (toInternal.{u + 1, u, u}.obj (chaoticStructureSheaf X))) :=
  toInternalForgetIso.{u + 1, u, u}.hom.app (chaoticStructureSheaf Y) ≫
    (chaoticToposHom f).adjunction.homEquiv _ _ (chaoticInverseImageStructureMap f) ≫
    (chaoticToposHom f).pushforward.map
      (toInternalForgetIso.{u + 1, u, u}.inv.app (chaoticStructureSheaf X)) ≫
    (chaoticToposHom f).internalRingDirectImageForgetIso.inv.app
      (toInternal.{u + 1, u, u}.obj (chaoticStructureSheaf X))

/-- The adjunct structure map preserves the canonical internal ring operations. -/
instance chaoticDirectStructureMap_isRingHom :
    @IsRingHom (Sheaf (⊥ : GrothendieckTopology Y.total) (Type u)) _ _
      (RingObjects.carrier ⊥ (toInternal.{u + 1, u, u}.obj (chaoticStructureSheaf Y)))
      (RingObjects.carrier ⊥ ((chaoticToposHom f).internalRingDirectImage.obj
        (toInternal.{u + 1, u, u}.obj (chaoticStructureSheaf X))))
      (RingObjects.ringObj ⊥ (toInternal.{u + 1, u, u}.obj
        (chaoticStructureSheaf Y))).toAddGrpObj.toAddMonObj
      (RingObjects.ringObj ⊥ ((chaoticToposHom f).internalRingDirectImage.obj
        (toInternal.{u + 1, u, u}.obj (chaoticStructureSheaf X)))).toAddGrpObj.toAddMonObj
      (RingObjects.ringObj ⊥ (toInternal.{u + 1, u, u}.obj (chaoticStructureSheaf Y))).toMonObj
      (RingObjects.ringObj ⊥ ((chaoticToposHom f).internalRingDirectImage.obj
        (toInternal.{u + 1, u, u}.obj (chaoticStructureSheaf X)))).toMonObj
      (chaoticDirectStructureMapUnderlying f) := sorry

/-- The adjunct structure map bundled as a morphism of internal rings. -/
def chaoticDirectStructureMapInternal :
    RingObjects.Hom (⊥ : GrothendieckTopology Y.total)
      (toInternal.{u + 1, u, u}.obj (chaoticStructureSheaf Y))
      ((chaoticToposHom f).internalRingDirectImage.obj
        (toInternal.{u + 1, u, u}.obj (chaoticStructureSheaf X))) :=
  @RingObjCat.Hom.mk (Sheaf (⊥ : GrothendieckTopology Y.total) (Type u)) _ _
    (sheafBraidedCategory ⊥) _ _
    (chaoticDirectStructureMapUnderlying f) (chaoticDirectStructureMap_isRingHom f)

/-- The canonical direct-image structure map of ring-valued sheaves, reconstructed from
its internal-ring morphism. -/
def chaoticDirectStructureMap :
    chaoticStructureSheaf Y ⟶
      (chaoticToposHom f).ringDirectImage.obj (chaoticStructureSheaf X) :=
  toFromIso.{u + 1, u, u}.inv.app (chaoticStructureSheaf Y) ≫
    fromInternal.{u + 1, u, u}.map (chaoticDirectStructureMapInternal f)

/-- Direct image of presheaves of modules along a 1-morphism
`f : X ⟶ Y`, obtained from geometric direct image and canonical restriction of scalars. -/
abbrev presheafModulePushforward {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P] :
    PresheafOfModules.{u} (structureSheaf X).obj ⥤
      PresheafOfModules.{u} (structureSheaf Y).obj :=
  (SheafOfModules.Bottom.equivalence (chaoticStructureSheaf X)).inverse ⋙
    (chaoticToposHom f).moduleDirectImage (chaoticStructureSheaf X) ⋙
    SheafOfModules.restrictScalars (chaoticDirectStructureMap f) ⋙
    (SheafOfModules.Bottom.equivalence (chaoticStructureSheaf Y)).functor

/-- After forgetting to abelian presheaves, module direct image is isomorphic to
right Kan extension along `(toFunctor f).op`. -/
theorem presheafModulePushforward_toPresheaf {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : X.totalᵒᵖ ⥤ Ab, HasRightKanExtension (toFunctor f).op P] :
    Nonempty
      (presheafModulePushforward f ⋙
          PresheafOfModules.toPresheaf (structureSheaf Y).obj ≅
        PresheafOfModules.toPresheaf (structureSheaf X).obj ⋙
          (toFunctor f).op.ran) := sorry

end AlgebraicGeometry.GroupoidsOver
