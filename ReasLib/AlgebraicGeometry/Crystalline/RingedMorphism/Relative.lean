/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Module.Coefficients
public import ReasLib.AlgebraicGeometry.Crystalline.Cohomology.BaseSections
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Adjunction
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction.Composition
public import ReasLib.AlgebraicGeometry.Crystalline.Functoriality
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfSite
public import ReasLib.AlgebraicGeometry.Crystalline.Topos
public import ReasLib.AlgebraicGeometry.Crystalline.RingedMorphism

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline CrystallineCoefficients
open ComplexShape

universe u

namespace CrystallineRingedGeometry

variable {S X : Scheme.{u}} (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (hc : ∀ (V : S.affineOpens) (f : Γ(S, V)),
  (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
    (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (x₀ : X ⟶ I.subscheme)

/-- A big crystalline object retains its actual thickening over the base. -/
def bigThickeningOverBase : RelativeCRIS S I γ hc X x₀ ⥤ Over S where
  obj T := Over.mk T.1.thickeningToBase
  map f := Over.homMk f.thickening f.base_comm
  map_id := by intro T; rfl
  map_comp := by intro T U V f g; rfl

/-- Lifted thickening functions satisfy descent on the big crystalline site. -/
theorem bigStructureSheaf_isSheaf :
    Presheaf.IsSheaf (crystallineZariskiTopology S I γ hc X x₀)
      (Presheaf.ringPresheafOfComm
        (Scheme.Over.commStructurePresheaf (bigThickeningOverBase I γ hc x₀))) := sorry

/-- The structure sheaf on the big crystalline site, lifted without changing
its functions or restriction maps. -/
noncomputable def bigStructureSheaf :
    Sheaf (crystallineZariskiTopology S I γ hc X x₀) RingCat.{u + 1} :=
  ⟨Presheaf.ringPresheafOfComm
    (Scheme.Over.commStructurePresheaf (bigThickeningOverBase I γ hc x₀)),
    bigStructureSheaf_isSheaf I γ hc x₀⟩

/-- The genuine big crystalline ringed site. -/
noncomputable abbrev bigRingedSite : RingedSite.{u + 1, u, u + 1} :=
  RingedSite.ofRingSheaf (crystallineZariskiTopology S I γ hc X x₀)
    (bigStructureSheaf I γ hc x₀)

/-- Open coverings of a thickening lift to crystalline coverings by restricting
the source, the thickening, and its divided powers to each open. -/
instance bigThickeningOverBase_isCocontinuous :
    (bigThickeningOverBase I γ hc x₀).IsCocontinuous
      (crystallineZariskiTopology S I γ hc X x₀)
      (StandardTopology.zariski.overTopology S) := sorry

/-- The structure-presheaf map to the base Zariski site is the identity on
functions of the actual thickening over `S`. -/
noncomputable def baseStructureMap :
    (bigThickeningOverBase I γ hc x₀).op ⋙
        (Scheme.AssociatedModule.bigCommRingedSite .zariski S).structureSheaf.obj ⟶
      (bigStructureSheaf I γ hc x₀).obj where
  app T := 𝟙 _
  naturality := by intro T U k; rfl

/-- The structure morphism from the big crystalline ringed topos to the big
Zariski ringed topos of the base is induced by the actual thickening over `S`. -/
noncomputable def bigStructureMorphism
    [HasSheafify (crystallineZariskiTopology S I γ hc X x₀) (Type (u + 1))]
    [∀ P : (RelativeCRIS S I γ hc X x₀)ᵒᵖ ⥤ Type (u + 1),
      (bigThickeningOverBase I γ hc x₀).op.HasPointwiseRightKanExtension P]
    [(crystallineZariskiTopology S I γ hc X x₀).HasSheafCompose (forget RingCat.{u + 1})] :
    RingedSite.ToposHom (bigRingedSite I γ hc x₀)
      (Scheme.AssociatedModule.bigCommRingedSite .zariski S) :=
  @RingedSite.Cocontinuous.toRingedTopos (bigRingedSite I γ hc x₀)
    (Scheme.AssociatedModule.bigCommRingedSite .zariski S)
    (bigThickeningOverBase I γ hc x₀)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (baseStructureMap I γ hc x₀)

variable {p : ℕ} [Fact p.Prime]
variable {S' Y : Scheme.{u}} (I' : S'.IdealSheafData)
variable (γ' : ∀ V : S'.affineOpens, DividedPowers (I'.ideal V))
variable (hc' : ∀ (V : S'.affineOpens) (f : Γ(S', V)),
  (γ' V).IsDPMorphism (γ' (S'.affineBasicOpen f))
    (S'.presheaf.map (homOfLE (S'.basicOpen_le f)).op).hom)
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (s' : S' ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (y₀ : Y ⟶ I'.subscheme) (f : X ⟶ Y)
variable (g : DividedPowerSchemeHom I I' s s') (hf : f ≫ y₀ = x₀ ≫ g.zeroFiberMap)
variable (hpX : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable (hpY : ∀ U : Y.affineOpens, IsNilpotent (p : Γ(Y, U)))
variable (hγ : ∀ (V : S'.affineOpens) (W : S.affineOpens)
  (hVW : W.1 ≤ g.base ⁻¹ᵁ V.1),
  (γ' V).IsDPMorphism (γ W) (g.base.appLE V W hVW).hom)

/-- The crystalline functor changes the base of a thickening but retains
its ring of functions; hence its structure-presheaf map is the identity. -/
noncomputable def bigStructureMap :
    (CrystallineFunctor.of f g hf hpX hpY hγ).toRelativeFunctor.op ⋙
        (bigStructureSheaf I' γ' hc' y₀).obj ⟶ (bigStructureSheaf I γ hc x₀).obj where
  app T := 𝟙 _
  naturality := by intro T U k; rfl

variable [HasSheafify (crystallineZariskiTopology S I γ hc X x₀) (Type (u + 1))]
variable [∀ P : (RelativeCRIS S I γ hc X x₀)ᵒᵖ ⥤ Type (u + 1),
  (CrystallineFunctor.of f g hf hpX hpY hγ).toRelativeFunctor.op.HasPointwiseRightKanExtension P]
variable [(crystallineZariskiTopology S I γ hc X x₀).HasSheafCompose (forget RingCat.{u + 1})]
variable [(crystallineZariskiTopology S' I' γ' hc' Y y₀).HasSheafCompose (forget RingCat.{u + 1})]

/-- The ringed geometric morphism of big crystalline topoi induced by the
actual scheme and divided-power-base maps. No arbitrary structure map is used. -/
noncomputable def bigRingedMorphism :
    RingedSite.ToposHom (bigRingedSite I γ hc x₀) (bigRingedSite I' γ' hc' y₀) :=
  @RingedSite.Cocontinuous.toRingedTopos
    (bigRingedSite I γ hc x₀) (bigRingedSite I' γ' hc' y₀)
    (CrystallineFunctor.of f g hf hpX hpY hγ).toRelativeFunctor
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (bigStructureMap I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ)

/-- Restricting the big structure presheaf along the small-site inclusion
retains the same thickening and the same functions. -/
noncomputable def smallStructureMap :
    (smallCrystallineInclusion S I γ hc X x₀).op ⋙ (bigStructureSheaf I γ hc x₀).obj ⟶
      (CrystallineCoefficients.liftedStructureSheaf I γ hc x₀ p s hpX).obj where
  app T := 𝟙 _
  naturality := by intro T U k; rfl

variable [HasSheafify (smallCrystallineTopology p S I γ hc s X x₀ hpX) (Type (u + 1))]
variable [∀ P : (smallCrystallineSite S I γ hc X x₀)ᵒᵖ ⥤ Type (u + 1),
  (smallCrystallineInclusion S I γ hc X x₀).op.HasPointwiseRightKanExtension P]
variable [(smallCrystallineTopology p S I γ hc s X x₀ hpX).HasSheafCompose
  (forget RingCat.{u + 1})]

/-- The small-to-big crystalline inclusion with its canonical ring structure. -/
noncomputable def smallToBigRinged :
    RingedSite.ToposHom (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX)
      (bigRingedSite I γ hc x₀) :=
  @RingedSite.Cocontinuous.toRingedTopos
    (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX) (bigRingedSite I γ hc x₀)
    (smallCrystallineInclusion S I γ hc X x₀)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (smallStructureMap I γ hc x₀ s hpX)

/-- The small crystalline structure morphism, using the canonical inclusion
into the big crystalline ringed topos before passing to the base. -/
noncomputable def structureMorphism
    [∀ P : (RelativeCRIS S I γ hc X x₀)ᵒᵖ ⥤ Type (u + 1),
      (bigThickeningOverBase I γ hc x₀).op.HasPointwiseRightKanExtension P] :
    RingedSite.ToposHom (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX)
      (Scheme.AssociatedModule.bigCommRingedSite .zariski S) :=
  RingedSite.ToposHom.comp (smallToBigRinged I γ hc x₀ s hpX)
    (bigStructureMorphism I γ hc x₀)

/-- The crystalline structure morphism to the base's small Zariski ringed
topos, with both the site bridge and the structure map retained. -/
noncomputable def structureMorphismToSmall
    [∀ P : (RelativeCRIS S I γ hc X x₀)ᵒᵖ ⥤ Type (u + 1),
      (bigThickeningOverBase I γ hc x₀).op.HasPointwiseRightKanExtension P] :
    RingedSite.ToposHom (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX)
      (Scheme.AssociatedModule.smallCommRingedSite .zariski S) :=
  RingedSite.ToposHom.comp (structureMorphism I γ hc x₀ s hpX) (AlgebraicGeometry.Scheme.Crystalline.Ringed.baseSmallProjection S)

variable [∀ P : (smallCrystallineSite S I γ hc X x₀)ᵒᵖ ⥤ Type (u + 1),
  (smallCrystallineInclusion S I γ hc X x₀).op.HasLeftKanExtension P]

/-- Ring-valued direct image of the big-to-small projection is restriction. -/
noncomputable abbrev bigToSmallRingPush :
    Sheaf (crystallineZariskiTopology S I γ hc X x₀) RingCat.{u + 1} ⥤
      Sheaf (smallCrystallineTopology p S I γ hc s X x₀ hpX) RingCat.{u + 1} :=
  (smallCrystallineInclusion S I γ hc X x₀).sheafPushforwardContinuous RingCat.{u + 1}
    (smallCrystallineTopology p S I γ hc s X x₀ hpX)
    (crystallineZariskiTopology S I γ hc X x₀)

/-- Restriction commutes definitionally with forgetting the ring operations. -/
noncomputable def bigToSmallForgetIso :
    bigToSmallRingPush I γ hc x₀ s hpX ⋙
        sheafCompose (smallCrystallineTopology p S I γ hc s X x₀ hpX)
          (forget RingCat.{u + 1}) ≅
      sheafCompose (crystallineZariskiTopology S I γ hc X x₀) (forget RingCat.{u + 1}) ⋙
        (bigToSmallCrystallineToposMorphism S I γ hc X x₀ p s hpX).pushforward :=
  Iso.refl _

/-- The restricted big structure sheaf agrees with the small structure sheaf. -/
noncomputable def bigToSmallStructureMap :
    CrystallineCoefficients.liftedStructureSheaf I γ hc x₀ p s hpX ⟶
      (bigToSmallRingPush I γ hc x₀ s hpX).obj (bigStructureSheaf I γ hc x₀) where
  hom := { app := fun T ↦ 𝟙 _
           naturality := by intro T U k; rfl }

/-- The identity-on-functions structure map preserves the internal ring
operations of continuous direct image. -/
theorem bigToSmallRingCompatible :
    @RingedSite.ToposHom.Direct.IsRingCompatible
      (bigRingedSite I γ hc x₀) (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX)
      inferInstance inferInstance
      (bigToSmallCrystallineToposMorphism S I γ hc X x₀ p s hpX)
      (bigToSmallRingPush I γ hc x₀ s hpX)
      (bigToSmallForgetIso I γ hc x₀ s hpX)
      (bigToSmallStructureMap I γ hc x₀ s hpX) := sorry

/-- The big-to-small projection as a genuine morphism of ringed topoi. -/
noncomputable def bigToSmallRinged :
    RingedSite.ToposHom (bigRingedSite I γ hc x₀)
      (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX) :=
  @RingedSite.ToposHom.ofDirectImage
    (bigRingedSite I γ hc x₀) (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX)
    inferInstance inferInstance
    (bigToSmallCrystallineToposMorphism S I γ hc X x₀ p s hpX)
    (bigToSmallRingPush I γ hc x₀ s hpX)
    (bigToSmallForgetIso I γ hc x₀ s hpX)
    (bigToSmallStructureMap I γ hc x₀ s hpX)
    (bigToSmallRingCompatible I γ hc x₀ s hpX)

variable [HasSheafify (crystallineZariskiTopology S' I' γ' hc' Y y₀) (Type (u + 1))]
variable [∀ P : (smallCrystallineSite S' I' γ' hc' Y y₀)ᵒᵖ ⥤ Type (u + 1),
  (smallCrystallineInclusion S' I' γ' hc' Y y₀).op.HasLeftKanExtension P]
variable [(smallCrystallineTopology p S' I' γ' hc' s' Y y₀ hpY).HasSheafCompose
  (forget RingCat.{u + 1})]

/-- The geometric small crystalline morphism, including the structure-sheaf
maps, is the composite `π_Y ∘ f_CRIS ∘ i_X`. -/
noncomputable def smallRingedMorphism :
    RingedSite.ToposHom (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX)
      (CrystallineCoefficients.liftedRingedSite I' γ' hc' y₀ p s' hpY) :=
  RingedSite.ToposHom.comp (smallToBigRinged I γ hc x₀ s hpX)
    (RingedSite.ToposHom.comp
      (bigRingedMorphism I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ)
      (bigToSmallRinged I' γ' hc' y₀ s' hpY))

/-- The actual crystalline morphism respects the base-ring actions: both
routes pull a base function back along the thickening's structure morphism.
This fixes the semilinearity used in the cohomology comparison, rather than
assuming an arbitrary comparison isomorphism. -/
theorem baseActions_compatible :
    (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ).globalSectionsMap.hom.comp
        (CrystallineCoefficients.baseToGlobalSections I' γ' hc' y₀ p s' hpY) =
      (CrystallineCoefficients.baseToGlobalSections I γ hc x₀ p s hpX).comp
        (CrystallineCoefficients.baseRingMap g.base) := sorry

end CrystallineRingedGeometry
