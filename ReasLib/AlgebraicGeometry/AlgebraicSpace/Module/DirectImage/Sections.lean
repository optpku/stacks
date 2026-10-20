module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage

/-! # Direct images of compatible sections -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TypeCat TopCat AlgebraicGeometry
open TopologicalSpace
open AlgebraicGeometry.AlgebraicSpace

noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace

private theorem directImageSectionCone_naturality {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (F : Sheaf (smallEtaleTopology X) (Type u)) (s : F.obj.sections)
    (V : smallEtaleSite Y) :
    ∀ ⦃a b : StructuredArrow (op ((etaleBaseChange f).obj V))
        (SpacesEtale.AtlasCharts.inclusion X).op⦄ (g : a ⟶ b),
      𝟙 (PUnit : Type u) ≫
        TypeCat.ofHom (fun _ : PUnit ↦
          s.1 (op ((SmallEtale.AtlasCharts.inclusion X).obj b.right.unop))) =
      TypeCat.ofHom (fun _ : PUnit ↦
          s.1 (op ((SmallEtale.AtlasCharts.inclusion X).obj a.right.unop))) ≫
        (StructuredArrow.proj (op ((etaleBaseChange f).obj V))
      (SpacesEtale.AtlasCharts.inclusion X).op ⋙ ((EtaleTopos.smallEquivalence X).functor.obj F).obj).map g :=
  sorry

/-- A compatible section gives a constant-vertex cone over the right-Kan
diagram used by the explicit direct image on type-valued sheaves. -/
private noncomputable def directImageSectionCone {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (F : Sheaf (smallEtaleTopology X) (Type u)) (s : F.obj.sections)
    (V : smallEtaleSite Y) :
    Cone (StructuredArrow.proj (op ((etaleBaseChange f).obj V))
      (SpacesEtale.AtlasCharts.inclusion X).op ⋙ ((EtaleTopos.smallEquivalence X).functor.obj F).obj) where
  pt := PUnit
  π := { app := fun a ↦ TypeCat.ofHom
           (fun _ ↦ s.1 (op ((SmallEtale.AtlasCharts.inclusion X).obj a.right.unop)))
         naturality := directImageSectionCone_naturality f F s V }

private theorem typeDirectImageSection_compatible {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (F : Sheaf (smallEtaleTopology X) (Type u)) (s : F.obj.sections) :
    (fun (V : (smallEtaleSite Y)ᵒᵖ) ↦
      (((SpacesEtale.AtlasCharts.inclusion X).op.ranObjObjIsoLimit
        ((EtaleTopos.smallEquivalence X).functor.obj F).obj
      (op ((etaleBaseChange f).obj V.unop))).inv
        ((limit.lift _ (directImageSectionCone f F s V.unop)) PUnit.unit))) ∈ ((typePushforward f).obj F).obj.sections :=
  sorry

/-- Direct image of a compatible section, formed by the explicit limit lift
in each right-Kan fiber, rather than by a chosen inverse-image adjunction. -/
@[no_expose] noncomputable def typeDirectImageSection {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (F : Sheaf (smallEtaleTopology X) (Type u)) (s : F.obj.sections) :
    ((typePushforward f).obj F).obj.sections :=
  ⟨fun V ↦
      (((SpacesEtale.AtlasCharts.inclusion X).op.ranObjObjIsoLimit
        ((EtaleTopos.smallEquivalence X).functor.obj F).obj
      (op ((etaleBaseChange f).obj V.unop))).inv
        ((limit.lift _ (directImageSectionCone f F s V.unop)) PUnit.unit)), typeDirectImageSection_compatible f F s⟩

private theorem moduleDirectImageSection_compatible
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (F : X.Modules) (s : F.sections) :
    (fun (V : (smallEtaleSite Y)ᵒᵖ) ↦
      (((RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom f)).inv.app F).hom.app V)
        ((typeDirectImageSection f
          ((Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj F) s).1 V)) ∈
      (((Modules.pushforward f).obj F).val.presheaf ⋙ forget _).sections :=
  sorry

/-- The direct image of a module section uses the specified type-valued
direct image and the actual forgetful comparison for module direct image. -/
noncomputable def moduleDirectImageSection {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (F : X.Modules) (s : F.sections) :
    ((Modules.pushforward f).obj F).sections :=
  let t := typeDirectImageSection f
    ((Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj F) s
  ⟨fun V ↦
    (((RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom f)).inv.app F).hom.app V)
      (t.1 V), by exact moduleDirectImageSection_compatible f F s⟩

end AlgebraicGeometry.AlgebraicSpace
