/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.Comparison
public import ReasLib.AlgebraicGeometry.RingedSpace.Morphism.Thickening.IdealTensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatLift
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatMorphism
public import ReasLib.AlgebraicGeometry.RingedSpace.Morphism.Thickening.Strict
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Obstructions to relatively flat module lifts

The identity infinitesimal obstruction and the canonical ideal tensor comparison
characterize relatively flat lifts along strict morphisms of first-order thickenings.

The reused `tensorSection`, module monoidal, symmetric and closed structures,
`unitIsoTensorUnit`, and automatic pullback monoidal APIs remain an explicit-data
follow-up: the constructions here expose certificates for their own exactness
and compatibility facts without changing that underlying infrastructure.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace (Modules)
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Modules
open AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening
namespace Hom

variable {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]
variable (g : T ⟶ U) (F : T.left.Modules)

/-- For a strict morphism of first-order thickenings and a relatively flat module, a
flat lift exists exactly when the canonical ideal tensor comparison is an isomorphism
and the infinitesimal obstruction for the identity comparison vanishes. -/
theorem exists_flatLift_iff [SheafOfModules.IsFlatOver F g.left] (hg : IsStrict g)
    [HasExt.{u} T.left.Modules] :
    Nonempty (FlatLift g F) ↔
      IsIso (sourceIdealTensorMap g F) ∧
        existenceObstruction T.hom F (idealModule T.hom ⊗ F)
          (identityInfinitesimalMap T.hom F) = 0 := sorry

end Hom
end AlgebraicGeometry.RingedSpace.Thickening

namespace AlgebraicGeometry.RingedSpace.Thickening.Hom.FlatLift

variable {T U : Thickening.{u}} [IsFirstOrderThickening T.hom]
  [IsFirstOrderThickening U.hom] {g : T ⟶ U}

/-- For a strict morphism of first-order thickenings with flat upper morphism,
the pulled-back base ideal maps isomorphically to the kernel ideal. -/
theorem isIso_sourceIdealMap (hg : IsStrict g) [RingedSpace.Hom.IsFlat g.right] :
    IsIso (sourceIdealMap g) := by
  have inclusionMono : Mono ((RingedSpace.Hom.pullback g.right).map
      (Thickening.ker U).arrow) :=
    @preserves_mono_of_preservesLimit _ _ _ _ (RingedSpace.Hom.pullback g.right)
      _ _ (Thickening.ker U).arrow
      ((RingedSpace.Hom.pullback_preservesFiniteLimits_of_isFlat g.right).preservesFiniteLimits
        Limits.WalkingCospan).preservesLimit inferInstance
  have pullbackMono : Mono ((Thickening.ker U).pullbackMap g.right) :=
    mono_comp' inclusionMono
      (inferInstanceAs (Mono (SheafOfModules.pullbackObjUnitToUnit
        (RingedSpace.Hom.toRingCatSheafHom g.right))))
  have comparisonMono : Mono (idealMap g) :=
    @mono_of_mono_fac _ _ _ _ _ _ _ _ pullbackMono
      (Subobject.factorThru_arrow (Thickening.ker T) _ (idealMap_factors g))
  have comparisonIso : IsIso (idealMap g) :=
    @isIso_of_mono_of_epi _ _ inferInstance _ _ (idealMap g) comparisonMono hg
  unfold sourceIdealMap
  exact IsIso.comp_isIso'
    ((RingedSpace.Hom.pullbackCompIso g.left U.hom).app _).isIso_inv <|
    IsIso.comp_isIso' ((eqToIso _).app _).isIso_hom <|
    IsIso.comp_isIso' ((RingedSpace.Hom.pullbackCompIso T.hom g.right).app _).isIso_hom
      (@Functor.map_isIso _ _ _ _ _ _ (T.hom^*) (idealMap g) comparisonIso)

/-- Tensoring the ideal comparison of a strict morphism with flat upper morphism
by any module gives an isomorphism. -/
theorem isIso_sourceIdealTensorMap (hg : IsStrict g) [RingedSpace.Hom.IsFlat g.right]
    (F : T.left.Modules) : IsIso (sourceIdealTensorMap g F) := by
  exact @MonoidalCategory.tensor_isIso _ _ _ _ _ _ _ (sourceIdealMap g)
    (isIso_sourceIdealMap hg) (𝟙 F) inferInstance

/-- The canonical isomorphism from the pulled-back base ideal tensor a module to
the kernel ideal tensor that module, for a strict morphism with flat upper morphism. -/
def sourceIdealTensorIso (hg : IsStrict g) [RingedSpace.Hom.IsFlat g.right]
    (F : T.left.Modules) :
    (g.left^*).obj (idealModule U.hom) ⊗ F ≅ idealModule T.hom ⊗ F :=
  @asIso _ _ _ _ (sourceIdealTensorMap g F) (isIso_sourceIdealTensorMap hg F)

end AlgebraicGeometry.RingedSpace.Thickening.Hom.FlatLift

namespace AlgebraicGeometry.RingedSpace.Modules

open AlgebraicGeometry.RingedSpace.Thickening
open AlgebraicGeometry.RingedSpace.Thickening.Hom

variable {T U : Thickening.{u}} [IsFirstOrderThickening T.hom]
  [IsFirstOrderThickening U.hom]

/-- The identity infinitesimal comparison with pulled-back base-ideal coefficients
is the inverse ideal tensor comparison transported through the adjunction. -/
def relativeIdentityInfinitesimalMap (g : T ⟶ U) (hg : IsStrict g)
    [RingedSpace.Hom.IsFlat g.right] (F : T.left.Modules) :
    kernelIdealSheaf T.hom ⊗ (T.hom _*).obj F ⟶
      (T.hom _*).obj ((g.left^*).obj (idealModule U.hom) ⊗ F) :=
  infinitesimalMap_ofRestrict T.hom (FlatLift.sourceIdealTensorIso hg F).inv

end AlgebraicGeometry.RingedSpace.Modules

namespace AlgebraicGeometry.RingedSpace.Thickening.Hom.FlatLift

variable {T U : Thickening.{u}} [IsFirstOrderThickening T.hom]
  [IsFirstOrderThickening U.hom] {g : T ⟶ U} {F : T.left.Modules}

/-- The relative ideal inclusion of a flat lift transports the base-ideal tensor
comparison through pushforward and then applies the kernel-ideal action. -/
def relativeExtensionInclusion (hg : IsStrict g)
    [RingedSpace.Hom.IsFlat g.right] (L : FlatLift g F) :
    (T.hom _*).obj ((g.left^*).obj (idealModule U.hom) ⊗ F) ⟶ L.module :=
  (T.hom _*).map (sourceIdealTensorIso hg F).hom ≫
    (T.hom _*).map
      (tensorHom (C := T.left.Modules) (𝟙 (idealModule T.hom)) L.restrictIso.inv ≫
        actionToIdealMulRestrict T.hom L.module) ≫
      (idealMulUnitInv T.hom L.module ≫ idealMulι T.hom L.module)

/-- The relative extension projection is the adjunction transpose of the
specified reduction isomorphism of a flat lift. -/
def relativeExtensionProjection (L : FlatLift g F) :
    L.module ⟶ (T.hom _*).obj F :=
  (pullbackPushforwardAdjunction T.hom).homEquiv L.module F L.restrictIso.hom

/-- The canonical relative inclusion and projection form a short exact sequence
with the relative identity infinitesimal map. This certificate records exactness
and compatibility facts for the fixed maps, without supplying any new data. -/
def RelativeExtensionCertificate (hg : IsStrict g)
    [SheafOfModules.IsFlatOver F g.left] [RingedSpace.Hom.IsFlat g.right]
    (L : FlatLift g F) : Prop :=
  ∃ (w : relativeExtensionInclusion hg L ≫ relativeExtensionProjection L = 0)
    (hSE : (ShortComplex.mk (relativeExtensionInclusion hg L)
      (relativeExtensionProjection L) w).ShortExact),
    infinitesimalMap T.hom (relativeExtensionInclusion hg L)
      (relativeExtensionProjection L) w hSE = relativeIdentityInfinitesimalMap g hg F

/-- The canonical maps of a relatively flat lift satisfy relative exactness and
infinitesimal compatibility. -/
theorem relativeExtension_certificate (hg : IsStrict g)
    [SheafOfModules.IsFlatOver F g.left] [RingedSpace.Hom.IsFlat g.right]
    (L : FlatLift g F) : RelativeExtensionCertificate hg L := sorry

/-- A flat lift gives its relative infinitesimal extension using the canonical
maps and an explicit certificate of their exactness and compatibility. -/
def toRelativeInfinitesimalExtensionOf (hg : IsStrict g)
    [SheafOfModules.IsFlatOver F g.left] [RingedSpace.Hom.IsFlat g.right]
    (L : FlatLift g F) (hRel : RelativeExtensionCertificate hg L) :
    InfinitesimalExtension T.hom F ((g.left^*).obj (idealModule U.hom) ⊗ F)
      (relativeIdentityInfinitesimalMap g hg F) := by
  have w : relativeExtensionInclusion hg L ≫ relativeExtensionProjection L = 0 := by
    obtain ⟨w, _⟩ := hRel
    exact w
  have hSE : (ShortComplex.mk (relativeExtensionInclusion hg L)
      (relativeExtensionProjection L) w).ShortExact := by
    obtain ⟨_, hSE, _⟩ := hRel
    exact hSE
  have hc : infinitesimalMap T.hom (relativeExtensionInclusion hg L)
      (relativeExtensionProjection L) w hSE = relativeIdentityInfinitesimalMap g hg F := by
    obtain ⟨_, _, hc⟩ := hRel
    exact hc
  exact {
    module := L.module
    ι := relativeExtensionInclusion hg L
    π := relativeExtensionProjection L
    w := w
    shortExact := hSE
    infMap_eq := hc }

/-- The relative infinitesimal extension keeps the lifted module and has exactly
the canonical relative inclusion and reduction projection. -/
theorem toRelativeInfinitesimalExtensionOf_spec (hg : IsStrict g)
    [SheafOfModules.IsFlatOver F g.left] [RingedSpace.Hom.IsFlat g.right]
    (L : FlatLift g F) (hRel : RelativeExtensionCertificate hg L) :
    (toRelativeInfinitesimalExtensionOf hg L hRel).module = L.module ∧
      (toRelativeInfinitesimalExtensionOf hg L hRel).ι = relativeExtensionInclusion hg L ∧
      (toRelativeInfinitesimalExtensionOf hg L hRel).π = relativeExtensionProjection L :=
  ⟨rfl, rfl, rfl⟩

/-- The infinitesimal extension of a flat lift with pulled-back base-ideal
coefficients keeps its middle module and canonical relative maps. -/
def toRelativeInfinitesimalExtension (hg : IsStrict g)
    [SheafOfModules.IsFlatOver F g.left] [RingedSpace.Hom.IsFlat g.right]
    (L : FlatLift g F) :
    InfinitesimalExtension T.hom F ((g.left^*).obj (idealModule U.hom) ⊗ F)
      (relativeIdentityInfinitesimalMap g hg F) :=
  toRelativeInfinitesimalExtensionOf hg L (relativeExtension_certificate hg L)

/-- For a strict morphism of first-order thickenings with flat upper morphism,
a relatively flat module admits a flat lift exactly when its relative identity
obstruction with pulled-back base-ideal coefficients vanishes. -/
theorem exists_iff [SheafOfModules.IsFlatOver F g.left] [RingedSpace.Hom.IsFlat g.right]
    (hg : IsStrict g) [HasExt.{u} T.left.Modules] :
    Nonempty (FlatLift g F) ↔
      existenceObstruction T.hom F ((g.left^*).obj (idealModule U.hom) ⊗ F)
        (relativeIdentityInfinitesimalMap g hg F) = 0 := sorry

end AlgebraicGeometry.RingedSpace.Thickening.Hom.FlatLift
