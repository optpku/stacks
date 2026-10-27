/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Morphism.Thickening.FlatLift.Obstruction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatLift.RelativeTorsor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatLift.Automorphism
import StacksCheckRecall

/-!
# Flat lifts along a strict flat first-order thickening

In Situation 91.3.1, if `(f, f')` is strict, `f'` is flat, and `F` is flat over `S`
(which forces `ℐ = f^* 𝒥`), a flat `𝒪_{X'}`-lift of `F` exists iff the relative
identity obstruction in `Ext F (f^* 𝒥 ⊗ F) 2` vanishes. Isomorphism classes of lifts
are then a principal homogeneous space under `Ext F (f^* 𝒥 ⊗ F) 1`, and automorphisms
of a given lift pulling back to `id_F` are canonically `Ext F (f^* 𝒥 ⊗ F) 0`.

The existence criterion uses the canonical obstruction without presentation
certificates. The other conclusions accept certificates for exactness and
infinitesimal compatibility of the fixed relative maps and for invertibility of
the canonical source-ideal action and compatible endomorphisms. These are facts
proved in the source argument, rather than additional choices of modules or maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Abelian (Ext)
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace (Modules)
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Modules
open AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening.Hom.FlatLift

/- Lemma 91.6.1 (1)
A flat lift exists exactly when the relative identity obstruction with
coefficients in the pulled-back base ideal tensor the module vanishes. -/
@[stacks 08VR] #check (AlgebraicGeometry.RingedSpace.Thickening.Hom.FlatLift.exists_iff :
  ∀ {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]
    {g : T ⟶ U} {F : T.left.Modules} [SheafOfModules.IsFlatOver F g.left]
    [RingedSpace.Hom.IsFlat g.right] (hg : IsStrict g) [HasExt.{u} T.left.Modules],
    Nonempty (FlatLift g F) ↔
      existenceObstruction T.hom F ((g.left^*).obj (idealModule U.hom) ⊗ F)
        (relativeIdentityInfinitesimalMap g hg F) = 0)

/- Lemma 91.6.1 (2)
When a flat lift exists, its isomorphism classes form a principal homogeneous
space under Ext¹ with coefficients in the pulled-back base ideal tensor the module. -/
@[stacks 08VR] #check
  (AlgebraicGeometry.RingedSpace.Thickening.Hom.FlatLift.sourcePrincipalHomogeneousOf :
    ∀ {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]
      {g : T ⟶ U} {F : T.left.Modules} (hg : IsStrict g)
      [SheafOfModules.IsFlatOver F g.left] [RingedSpace.Hom.IsFlat g.right]
      [HasExt.{u} T.left.Modules]
      (hRel : ∀ L : FlatLift g F, RelativeExtensionCertificate hg L)
      (hD : ∀ L M : FlatLift g F, (sourceDifferenceRepresentativeOf hg hRel L M).ShortExact)
      (L0 : FlatLift g F),
      Nonempty (IsomorphismClass g F) ∧
        (∀ p : IsomorphismClass g F,
          Function.Bijective (fun q : IsomorphismClass g F => sourceDifferenceOf hg hRel hD q p)) ∧
        (∀ p q r : IsomorphismClass g F,
          sourceDifferenceOf hg hRel hD p r =
            sourceDifferenceOf hg hRel hD p q + sourceDifferenceOf hg hRel hD q r))

/- Lemma 91.6.1 (3)
Automorphisms of a fixed flat lift inducing the identity on its reduction
are canonically parametrized by Ext⁰ with pulled-back base-ideal coefficients. -/
@[stacks 08VR] #check (AlgebraicGeometry.RingedSpace.Thickening.Hom.FlatLift.autEquivOf :
  ∀ {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]
    {g : T ⟶ U} {F : T.left.Modules} (hg : IsStrict g)
    [SheafOfModules.IsFlatOver F g.left] [RingedSpace.Hom.IsFlat g.right]
    (L : FlatLift g F) [HasExt.{u} T.left.Modules]
    (hIdeal : IsIso (sourceIdealMulMap g L.module))
    (hAut : ∀ φ : Hom L L, IsIso φ.hom),
    Ext F ((g.left^*).obj (idealModule U.hom) ⊗ F) 0 ≃
      {φ : Hom L L // IsIso φ.hom})

variable {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]
variable {g : T ⟶ U} {F : T.left.Modules}

/- The based chart uses the specified flat lift as basepoint. -/
#check (AlgebraicGeometry.RingedSpace.Thickening.Hom.FlatLift.sourceIdealIsoClassEquivOf :
  ∀ {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]
    {g : T ⟶ U} {F : T.left.Modules} (hg : IsStrict g)
    [SheafOfModules.IsFlatOver F g.left] [RingedSpace.Hom.IsFlat g.right] (L0 : FlatLift g F)
    (hRel : RelativeExtensionCertificate hg L0),
    ExtensionClass ((g.left^*).obj (idealModule U.hom) ⊗ F) F ≃
      IsoClass T.hom F ((g.left^*).obj (idealModule U.hom) ⊗ F)
        (relativeIdentityInfinitesimalMap g hg F))

end AlgebraicGeometry.RingedSpace.Thickening.Hom.FlatLift
