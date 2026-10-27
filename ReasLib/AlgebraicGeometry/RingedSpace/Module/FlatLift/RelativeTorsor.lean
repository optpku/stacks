/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Morphism.Thickening.FlatLift.Obstruction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatLift.Torsor

/-!
# Relative Ext-valued differences of flat lifts

The canonical ideal comparison transports differences of flat lift classes to
Ext¹ with pulled-back base-ideal coefficients.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Abelian (Ext)
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Modules
open AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening.Hom.FlatLift

variable {T U : Thickening.{u}} [IsFirstOrderThickening T.hom]
  [IsFirstOrderThickening U.hom] {g : T ⟶ U} {F : T.left.Modules}

/-- The Baer difference of the canonical relative extensions of two flat lifts,
formed with explicit exactness and infinitesimal compatibility certificates. -/
def sourceDifferenceRepresentativeOf (hg : IsStrict g)
    [SheafOfModules.IsFlatOver F g.left] [RingedSpace.Hom.IsFlat g.right]
    (hRel : ∀ L : FlatLift g F, RelativeExtensionCertificate hg L)
    (L M : FlatLift g F) : ShortComplex T.left.Modules :=
  (InfinitesimalExtension.vsubExt (toRelativeInfinitesimalExtensionOf hg L (hRel L))
    (toRelativeInfinitesimalExtensionOf hg M (hRel M))).toShortComplex

/-- The descended Baer-difference complex of the relative infinitesimal extensions
associated to two flat lifts, with pulled-back base-ideal coefficients. -/
def sourceDifferenceRepresentative (hg : IsStrict g) [SheafOfModules.IsFlatOver F g.left]
    [RingedSpace.Hom.IsFlat g.right] (L M : FlatLift g F) : ShortComplex T.left.Modules :=
  sourceDifferenceRepresentativeOf hg (relativeExtension_certificate hg) L M

/-- The descended Baer-difference complex of two flat lifts is short exact. -/
theorem sourceDifferenceRepresentative_shortExact (hg : IsStrict g)
    [SheafOfModules.IsFlatOver F g.left] [RingedSpace.Hom.IsFlat g.right]
    (L M : FlatLift g F) : (sourceDifferenceRepresentative hg L M).ShortExact :=
  (InfinitesimalExtension.vsubExt (toRelativeInfinitesimalExtension hg L)
    (toRelativeInfinitesimalExtension hg M)).shortExact

/-- The relative Ext¹ difference of compatible lift classes is the class of
their canonical Baer difference, using supplied exactness certificates. -/
def sourceDifferenceOf (hg : IsStrict g) [SheafOfModules.IsFlatOver F g.left]
    [RingedSpace.Hom.IsFlat g.right] [HasExt.{u} T.left.Modules]
    (hRel : ∀ L : FlatLift g F, RelativeExtensionCertificate hg L)
    (hD : ∀ L M : FlatLift g F,
      (sourceDifferenceRepresentativeOf hg hRel L M).ShortExact)
    (p q : IsomorphismClass g F) :
    Ext F ((g.left^*).obj (idealModule U.hom) ⊗ F) 1 :=
  Quotient.liftOn₂ p q (fun L M => (hD L M).extClass) (by sorry)

/-- The difference of flat lift classes is the Ext¹ class of their descended
Baer-difference complex, formed with specified short-exactness certificates. -/
def sourceDifference (hg : IsStrict g) [SheafOfModules.IsFlatOver F g.left]
    [RingedSpace.Hom.IsFlat g.right] [HasExt.{u} T.left.Modules]
    (hD : ∀ L M : FlatLift g F, (sourceDifferenceRepresentative hg L M).ShortExact)
    (p q : IsomorphismClass g F) :
    Ext F ((g.left^*).obj (idealModule U.hom) ⊗ F) 1 :=
  sourceDifferenceOf hg (relativeExtension_certificate hg) hD p q

/-- For a strict morphism with flat upper morphism, the classes of flat lifts of a
relatively flat module, when inhabited, form a principal homogeneous space under
Ext¹ with pulled-back base-ideal coefficients: differences from every fixed class
are bijective and satisfy the additive cocycle identity. -/
theorem sourcePrincipalHomogeneousOf (hg : IsStrict g) [SheafOfModules.IsFlatOver F g.left]
    [RingedSpace.Hom.IsFlat g.right] [HasExt.{u} T.left.Modules]
    (hRel : ∀ L : FlatLift g F, RelativeExtensionCertificate hg L)
    (hD : ∀ L M : FlatLift g F, (sourceDifferenceRepresentativeOf hg hRel L M).ShortExact)
    (L0 : FlatLift g F) :
    Nonempty (IsomorphismClass g F) ∧
      (∀ p : IsomorphismClass g F,
        Function.Bijective (fun q : IsomorphismClass g F => sourceDifferenceOf hg hRel hD q p)) ∧
      (∀ p q r : IsomorphismClass g F,
        sourceDifferenceOf hg hRel hD p r =
          sourceDifferenceOf hg hRel hD p q + sourceDifferenceOf hg hRel hD q r) := sorry

/-- For a strict morphism with flat upper morphism, the classes of flat lifts of a
relatively flat module, when inhabited, form a principal homogeneous space under
Ext¹ with pulled-back base-ideal coefficients: differences from every fixed class
are bijective and satisfy the additive cocycle identity. -/
theorem sourcePrincipalHomogeneous (hg : IsStrict g) [SheafOfModules.IsFlatOver F g.left]
    [RingedSpace.Hom.IsFlat g.right] [HasExt.{u} T.left.Modules]
    (hD : ∀ L M : FlatLift g F, (sourceDifferenceRepresentative hg L M).ShortExact)
    (L0 : FlatLift g F) :
    Nonempty (IsomorphismClass g F) ∧
      (∀ p : IsomorphismClass g F,
        Function.Bijective (fun q : IsomorphismClass g F => sourceDifference hg hD q p)) ∧
      (∀ p q r : IsomorphismClass g F,
        sourceDifference hg hD p r = sourceDifference hg hD p q + sourceDifference hg hD q r) :=
  sourcePrincipalHomogeneousOf hg (relativeExtension_certificate hg) hD L0

/-- The based chart identifies extension classes with relative infinitesimal
extension classes using the extension associated to the specified flat lift. -/
def sourceIdealIsoClassEquivOf (hg : IsStrict g) [SheafOfModules.IsFlatOver F g.left]
    [RingedSpace.Hom.IsFlat g.right] (L0 : FlatLift g F)
    (hRel : RelativeExtensionCertificate hg L0) :
    ExtensionClass ((g.left^*).obj (idealModule U.hom) ⊗ F) F ≃
      IsoClass T.hom F ((g.left^*).obj (idealModule U.hom) ⊗ F)
        (relativeIdentityInfinitesimalMap g hg F) :=
  InfinitesimalExtension.isoClassEquiv (i := T.hom)
    (toRelativeInfinitesimalExtensionOf hg L0 hRel)

/-- The based chart identifies extension classes with relative infinitesimal
extension classes using the extension associated to the specified flat lift. -/
def sourceIdealIsoClassEquiv (hg : IsStrict g) [SheafOfModules.IsFlatOver F g.left]
    [RingedSpace.Hom.IsFlat g.right] (L0 : FlatLift g F) :
    ExtensionClass ((g.left^*).obj (idealModule U.hom) ⊗ F) F ≃
      IsoClass T.hom F ((g.left^*).obj (idealModule U.hom) ⊗ F)
        (relativeIdentityInfinitesimalMap g hg F) :=
  sourceIdealIsoClassEquivOf hg L0 (relativeExtension_certificate hg L0)

end AlgebraicGeometry.RingedSpace.Thickening.Hom.FlatLift
