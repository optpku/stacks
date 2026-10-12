/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ConstantCompletion
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Ideal
public import ReasLib.CategoryTheory.Sites.GlobalSections.ToposMorphism

/-!
# Constant-coefficient morphisms of ringed topoi

A morphism of topoi `Sh(D) ⟶ Sh(C)` together with the constant sheaf `underline(Λ)` on both
sites determines a morphism of ringed topoi
`(Sh(D), underline(Λ)) ⟶ (Sh(C), underline(Λ))`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MorphismOfTopoiIn
open RingedSite
open RingedSite.Hom
open RingedSite.Hom.ModuleDerived
open RingedSite.Hom.ModuleDerived.ConstantCompletion
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace RingedSite.ToposHom

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [JC.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [JD.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [JC.HasSheafCompose (forget RingCat.{u})]
variable [JD.HasSheafCompose (forget RingCat.{u})]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [HasWeakSheafify JD AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify JC CommRingCat.{u}]
variable [HasWeakSheafify JD CommRingCat.{u}]
variable [JC.WEqualsLocallyBijective CommRingCat.{u}]
variable [JD.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify JC RingCat.{u}]
variable [HasWeakSheafify JD RingCat.{u}]
variable [HasWeakSheafify JC (Type u)]
variable [HasWeakSheafify JD (Type u)]
variable [JC.PreservesSheafification (forget₂ CommRingCat.{u} RingCat.{u})]
variable [JD.PreservesSheafification (forget₂ CommRingCat.{u} RingCat.{u})]
variable [JC.PreservesSheafification (forget RingCat.{u})]
variable [JD.PreservesSheafification (forget RingCat.{u})]
variable [HasGlobalSectionsFunctor JC (Type u)]
variable [HasGlobalSectionsFunctor JD (Type u)]

/-- Forgetting the ring structure on `underline(Λ)` recovers the constant type-valued sheaf. -/
noncomputable def constantRingSheafUnderlyingIso
    {E : Type u} [SmallCategory E] (J : GrothendieckTopology E) (Λ : Type u)
    [CommRing Λ] [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.HasSheafCompose (forget RingCat.{u})] [HasWeakSheafify J CommRingCat.{u}]
    [HasWeakSheafify J RingCat.{u}] [HasWeakSheafify J (Type u)]
    [J.PreservesSheafification (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.PreservesSheafification (forget RingCat.{u})] :
    underlyingStructureSheaf (ofCommRingSheaf J (constantRingSheaf J Λ)) ≅
      (constantSheaf J (Type u)).obj Λ :=
  (sheafCompose J (forget RingCat.{u})).mapIso
      ((constantCommuteCompose J (forget₂ CommRingCat.{u} RingCat.{u})).app
        (CommRingCat.of Λ)) ≪≫
    (constantCommuteCompose J (forget RingCat.{u})).app
      ((forget₂ CommRingCat.{u} RingCat.{u}).obj (CommRingCat.of Λ))

/-- Inverse image of the underlying type-valued sheaf of `underline(Λ)` is identified with
the corresponding constant sheaf on the source topos. -/
noncomputable def ofConstantRingSheaf_underlyingMap (f : MorphismOfTopoiIn JC JD)
    (Λ : Type u) [CommRing Λ] :
    f.inverseImage.obj
        (underlyingStructureSheaf (ofCommRingSheaf JC (constantRingSheaf JC Λ))) ⟶
      underlyingStructureSheaf (ofCommRingSheaf JD (constantRingSheaf JD Λ)) :=
  (f.inverseImage.mapIso (constantRingSheafUnderlyingIso JC Λ)).hom ≫
    (constantSheafCompInverseImageIso f).hom.app Λ ≫
      (constantRingSheafUnderlyingIso JD Λ).inv

/-- The type-valued inverse-image comparison for `underline(Λ)`, after forgetting the
canonical ring inverse image. -/
noncomputable def ofConstantRingSheaf_ringUnderlyingMap (f : MorphismOfTopoiIn JC JD)
    (Λ : Type u) [CommRing Λ] :
    (sheafCompose JD (forget RingCat.{u})).obj
        (f.ringInverseImage.obj
          (ofCommRingSheaf JC (constantRingSheaf JC Λ)).structureSheaf) ⟶
      underlyingStructureSheaf (ofCommRingSheaf JD (constantRingSheaf JD Λ)) :=
  f.ringInverseImageForgetIso.hom.app
      (ofCommRingSheaf JC (constantRingSheaf JC Λ)).structureSheaf ≫
    ofConstantRingSheaf_underlyingMap f Λ

/-- The constant-ring inverse-image comparison preserves the multiplicative unit. -/
theorem ofConstantRingSheaf_map_one (f : MorphismOfTopoiIn JC JD)
    (Λ : Type u) [CommRing Λ] (U : Dᵒᵖ) :
    (ofConstantRingSheaf_ringUnderlyingMap f Λ).hom.app U
        (1 : (f.ringInverseImage.obj
          (ofCommRingSheaf JC (constantRingSheaf JC Λ)).structureSheaf).obj.obj U) =
      (1 : (ofCommRingSheaf JD (constantRingSheaf JD Λ)).structureSheaf.obj.obj U) := sorry

/-- The constant-ring inverse-image comparison preserves multiplication. -/
theorem ofConstantRingSheaf_map_mul (f : MorphismOfTopoiIn JC JD)
    (Λ : Type u) [CommRing Λ] (U : Dᵒᵖ)
    (a b : (f.ringInverseImage.obj
      (ofCommRingSheaf JC (constantRingSheaf JC Λ)).structureSheaf).obj.obj U) :
    (ofConstantRingSheaf_ringUnderlyingMap f Λ).hom.app U (a * b) =
      Mul.mul (α := (ofCommRingSheaf JD (constantRingSheaf JD Λ)).structureSheaf.obj.obj U)
        ((ofConstantRingSheaf_ringUnderlyingMap f Λ).hom.app U a) ((ofConstantRingSheaf_ringUnderlyingMap f Λ).hom.app U b) := sorry

/-- The constant-ring inverse-image comparison preserves zero. -/
theorem ofConstantRingSheaf_map_zero (f : MorphismOfTopoiIn JC JD)
    (Λ : Type u) [CommRing Λ] (U : Dᵒᵖ) :
    (ofConstantRingSheaf_ringUnderlyingMap f Λ).hom.app U
        (0 : (f.ringInverseImage.obj
          (ofCommRingSheaf JC (constantRingSheaf JC Λ)).structureSheaf).obj.obj U) =
      (0 : (ofCommRingSheaf JD (constantRingSheaf JD Λ)).structureSheaf.obj.obj U) := sorry

/-- The constant-ring inverse-image comparison preserves addition. -/
theorem ofConstantRingSheaf_map_add (f : MorphismOfTopoiIn JC JD)
    (Λ : Type u) [CommRing Λ] (U : Dᵒᵖ)
    (a b : (f.ringInverseImage.obj
      (ofCommRingSheaf JC (constantRingSheaf JC Λ)).structureSheaf).obj.obj U) :
    (ofConstantRingSheaf_ringUnderlyingMap f Λ).hom.app U (a + b) =
      Add.add (α := (ofCommRingSheaf JD (constantRingSheaf JD Λ)).structureSheaf.obj.obj U)
        ((ofConstantRingSheaf_ringUnderlyingMap f Λ).hom.app U a) ((ofConstantRingSheaf_ringUnderlyingMap f Λ).hom.app U b) := sorry

/-- The component ring homomorphism of the constant-coefficient inverse-image comparison. -/
noncomputable def ofConstantRingSheaf_structureMapApp (f : MorphismOfTopoiIn JC JD)
    (Λ : Type u) [CommRing Λ] (U : Dᵒᵖ) :
    (f.ringInverseImage.obj
      (ofCommRingSheaf JC (constantRingSheaf JC Λ)).structureSheaf).obj.obj U ⟶
      (ofCommRingSheaf JD (constantRingSheaf JD Λ)).structureSheaf.obj.obj U :=
  let source : RingCat.{u} :=
    (f.ringInverseImage.obj
      (ofCommRingSheaf JC (constantRingSheaf JC Λ)).structureSheaf).obj.obj U
  let target : RingCat.{u} :=
    (ofCommRingSheaf JD (constantRingSheaf JD Λ)).structureSheaf.obj.obj U
  @RingCat.ofHom source target source.ring target.ring
    { toFun := (ofConstantRingSheaf_ringUnderlyingMap f Λ).hom.app U
      map_one' := ofConstantRingSheaf_map_one f Λ U
      map_mul' := ofConstantRingSheaf_map_mul f Λ U
      map_zero' := ofConstantRingSheaf_map_zero f Λ U
      map_add' := ofConstantRingSheaf_map_add f Λ U }

/-- The component ring homomorphisms of the constant-coefficient comparison are natural. -/
theorem ofConstantRingSheaf_structureMap_naturality (f : MorphismOfTopoiIn JC JD)
    (Λ : Type u) [CommRing Λ] {U V : Dᵒᵖ} (g : U ⟶ V) :
    (f.ringInverseImage.obj
        (ofCommRingSheaf JC (constantRingSheaf JC Λ)).structureSheaf).obj.map g ≫
        ofConstantRingSheaf_structureMapApp f Λ V =
      ofConstantRingSheaf_structureMapApp f Λ U ≫
        (ofCommRingSheaf JD (constantRingSheaf JD Λ)).structureSheaf.obj.map g := sorry

/-- The inverse-image structure map of constant ring sheaves as a morphism of ring sheaves. -/
noncomputable def ofConstantRingSheaf_structureMap (f : MorphismOfTopoiIn JC JD)
    (Λ : Type u) [CommRing Λ] :
    f.ringInverseImage.obj (ofCommRingSheaf JC (constantRingSheaf JC Λ)).structureSheaf ⟶
      (ofCommRingSheaf JD (constantRingSheaf JD Λ)).structureSheaf where
  hom :=
    { app := ofConstantRingSheaf_structureMapApp f Λ
      naturality := fun _ _ g ↦ ofConstantRingSheaf_structureMap_naturality f Λ g }

/-- The morphism of ringed topoi `(Sh(D), underline(Λ)) ⟶ (Sh(C), underline(Λ))` attached to
a morphism of topoi `Sh(D) ⟶ Sh(C)`. -/
noncomputable def ofConstantRingSheaf (f : MorphismOfTopoiIn JC JD) (Λ : Type u)
    [CommRing Λ] :
    ToposHom (ofCommRingSheaf JD (constantRingSheaf JD Λ))
      (ofCommRingSheaf JC (constantRingSheaf JC Λ)) where
  toTopos := f
  structureMap := ofConstantRingSheaf_structureMap f Λ

/-- The underlying morphism of topoi of `ofConstantRingSheaf` is the given morphism. -/
theorem ofConstantRingSheaf_toTopos (f : MorphismOfTopoiIn JC JD) (Λ : Type u)
    [CommRing Λ] :
    (ofConstantRingSheaf f Λ).toTopos = f := sorry

/-- Forgetting rings, the structure map of `ofConstantRingSheaf` is the type-valued constant
sheaf comparison. -/
theorem ofConstantRingSheaf_structureMap_spec (f : MorphismOfTopoiIn JC JD)
    (Λ : Type u) [CommRing Λ] :
    (ofConstantRingSheaf f Λ).underlyingMap =
      ofConstantRingSheaf_underlyingMap f Λ := sorry

variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]

/-- The constant ideal sheaf of `I` is compatible with inverse image along
`ofConstantRingSheaf`. -/
theorem mapsConstantIdeal (f : MorphismOfTopoiIn JC JD) (I : Ideal Λ) :
    mapsIdeal.{u, u, u, u, u} (ofConstantRingSheaf f Λ) (constantIdealSheaf JC I)
      (constantIdealSheaf JD I) := sorry

/-- Among ideals on `D` compatible with the constant ideal of `I` on `C`, the constant ideal
of `I` on `D` is least. -/
theorem constantIdeal_isLeastMapsIdeal (f : MorphismOfTopoiIn JC JD) (I : Ideal Λ) :
    IsLeast
      { J' : Subobject (unitModule JD (constantRingSheaf JD Λ)) |
        mapsIdeal.{u, u, u, u, u} (ofConstantRingSheaf f Λ) (constantIdealSheaf JC I) J' }
      (constantIdealSheaf JD I) := sorry

end RingedSite.ToposHom
