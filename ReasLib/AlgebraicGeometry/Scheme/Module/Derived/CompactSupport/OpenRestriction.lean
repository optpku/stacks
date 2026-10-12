/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.ExtensionByZeroRestriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Proper

/-!
# Open restriction of compactly supported pushforward

This module constructs the three canonical comparisons of compactly supported derived
pushforward along an open of the source, and records that they agree.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.ObjectProperty.FullSubcategory
open DerivedCategory
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport

open Scheme.Compactification.Of

variable {S : Scheme.{u}} [IsNoetherian S]
variable {U X Y : Scheme.FiniteTypeSeparatedOver S}

/-- The source of a morphism of finite type separated schemes over a Noetherian base
is Noetherian after packaging it as an over-object. -/
theorem isNoetherian_mkHomLeft (f : X ⟶ Y) :
    IsNoetherian (Over.mk f.hom.left).left := by
  dsimp [Over.mk]
  infer_instance

/-- The compactification of a morphism of finite type separated schemes over a Noetherian
base is Noetherian. -/
theorem isNoetherian_compactification
    (f : X ⟶ Y)
    (P : Scheme.Compactification.Of (Over.left Y.obj) (Over.mk f.hom.left)) :
    IsNoetherian (Over.left P.obj.right) := by
  infer_instance

/-- Open immersions compose with the open immersion of a compactification. -/
theorem isOpenImmersion_comp_ι
    (i : U ⟶ X) [IsOpenImmersion i.hom.left] (f : X ⟶ Y)
    (P : Scheme.Compactification.Of (Over.left Y.obj) (Over.mk f.hom.left)) :
    IsOpenImmersion (i.hom.left ≫ ι P) :=
  @IsOpenImmersion.comp _ _ _ i.hom.left (ι P) inferInstance
    (Scheme.Compactification.Of.instIsOpenImmersion _ _ P)

/-- Bounded coherent restriction along an open of a morphism of finite type
separated schemes. -/
noncomputable def restriction_open (i : U ⟶ X) [IsOpenImmersion i.hom.left] :
    Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf] ⥤
      Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf] :=
  DeligneSystem.restriction i.hom.left

/-- Extension by zero along the open immersion of a compactification. -/
noncomputable def extensionByZero_ι (f : X ⟶ Y)
    (P : Scheme.Compactification.Of (Over.left Y.obj) (Over.mk f.hom.left)) :
    Dᵇ[SheafOfModules.isCoherent (Over.mk f.hom.left).left.ringCatSheaf] ⥤
      Pro Dᵇ[SheafOfModules.isCoherent (Over.left P.obj.right).ringCatSheaf] :=
  @DeligneSystem.extensionByZero _ _ (ι P)
    (isNoetherian_compactification f P) (isNoetherian_mkHomLeft f)
    (Scheme.Compactification.Of.instIsOpenImmersion _ _ P)

/-- Extension by zero along an open of the source composed with a compactification. -/
noncomputable def extensionByZero_comp_ι (i : U ⟶ X) [IsOpenImmersion i.hom.left]
    (f : X ⟶ Y)
    (P : Scheme.Compactification.Of (Over.left Y.obj) (Over.mk f.hom.left)) :
    Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf] ⥤
      Pro Dᵇ[SheafOfModules.isCoherent (Over.left P.obj.right).ringCatSheaf] :=
  @DeligneSystem.extensionByZero _ _ (i.hom.left ≫ ι P)
    (isNoetherian_compactification f P) inferInstance
    (isOpenImmersion_comp_ι i f P)

/-- The bounded-coherent represented Hom bifunctor determined by an upper-shriek
model. -/
noncomputable def boundedShriekHom (f : X ⟶ Y)
    (P : Scheme.Compactification.Of (Over.left Y.obj) (Over.mk f.hom.left))
    (A : Scheme.DerivedQCoh.PlusRightAdjoint (ambientMorphism P)) :
    (Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])ᵒᵖ ×
        Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf] ⥤ Type (u + 1) :=
  ((𝟭 _).prod (boundedToPlus (Over.left Y.obj))) ⋙
    shriekHom f P A.right A.adjunction A.plus A.compatibility

/-- Objectwise, `boundedShriekHom` is the Hom type from a bounded coherent object to
the chosen upper-shriek model. -/
theorem boundedShriekHom_obj (f : X ⟶ Y)
    (P : Scheme.Compactification.Of (Over.left Y.obj) (Over.mk f.hom.left))
    (A : Scheme.DerivedQCoh.PlusRightAdjoint (ambientMorphism P))
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])
    (L : Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf]) :
    (boundedShriekHom f P A).obj (Opposite.op K, L) =
      (shriekHom f P A.right A.adjunction A.plus A.compatibility).obj
        (Opposite.op K, (boundedToPlus (Over.left Y.obj)).obj L) := sorry

/-- The component function on Hom types induced by restricting the source and using
the upper-shriek restriction comparison. -/
noncomputable def shriekRestrictionHomApp (i : U ⟶ X) [IsOpenImmersion i.hom.left]
    (f : X ⟶ Y) (C : UpperShriekCompChoice i f)
    (shriekRestrictionIso :
      (upperShriekCoherentPlus f C.P_g C.A_g.right C.A_g.adjunction
          C.A_g.plus C.A_g.compatibility ⋙ Plus.CohomologyIn.ambient
            (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf)) ⋙
          RingedSpace.modulePullbackDerived (i.hom.left).toShHom ≅
        upperShriekCoherentPlus (i ≫ f) (comp i f C.P_g C.P_bar)
            C.A_fg.right C.A_fg.adjunction C.A_fg.plus C.A_fg.compatibility ⋙
          Plus.CohomologyIn.ambient
            (SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf))
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])
    (L : Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf]) :
    (boundedShriekHom f C.P_g C.A_g).obj (Opposite.op K, L) ⟶
      (boundedShriekHom (i ≫ f) (comp i f C.P_g C.P_bar) C.A_fg).obj
        (Opposite.op ((restriction_open i).obj K), L) :=
  ↾fun a ↦
    (DeligneSystem.restrictionAmbientIso i.hom.left).hom.app K ≫
      (RingedSpace.modulePullbackDerived (i.hom.left).toShHom).map a ≫
        shriekRestrictionIso.hom.app ((boundedToPlus (Over.left Y.obj)).obj L)

/-- Applying `shriekRestrictionHomApp` is restriction of the source morphism followed
by the specified upper-shriek bridge. -/
theorem shriekRestrictionHomApp_apply (i : U ⟶ X) [IsOpenImmersion i.hom.left]
    (f : X ⟶ Y) (C : UpperShriekCompChoice i f)
    (shriekRestrictionIso :
      (upperShriekCoherentPlus f C.P_g C.A_g.right C.A_g.adjunction
          C.A_g.plus C.A_g.compatibility ⋙ Plus.CohomologyIn.ambient
            (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf)) ⋙
          RingedSpace.modulePullbackDerived (i.hom.left).toShHom ≅
        upperShriekCoherentPlus (i ≫ f) (comp i f C.P_g C.P_bar)
            C.A_fg.right C.A_fg.adjunction C.A_fg.plus C.A_fg.compatibility ⋙
          Plus.CohomologyIn.ambient
            (SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf))
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])
    (L : Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf])
    (a : (boundedShriekHom f C.P_g C.A_g).obj (Opposite.op K, L)) :
    shriekRestrictionHomApp i f C shriekRestrictionIso K L a =
      (DeligneSystem.restrictionAmbientIso i.hom.left).hom.app K ≫
        (RingedSpace.modulePullbackDerived (i.hom.left).toShHom).map a ≫
          shriekRestrictionIso.hom.app ((boundedToPlus (Over.left Y.obj)).obj L) := sorry

/-- The componentwise upper-shriek restriction chain is natural in both bounded
coherent variables. -/
theorem shriekRestrictionHom_naturality (i : U ⟶ X) [IsOpenImmersion i.hom.left]
    (f : X ⟶ Y) (C : UpperShriekCompChoice i f)
    (shriekRestrictionIso :
      (upperShriekCoherentPlus f C.P_g C.A_g.right C.A_g.adjunction
          C.A_g.plus C.A_g.compatibility ⋙ Plus.CohomologyIn.ambient
            (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf)) ⋙
          RingedSpace.modulePullbackDerived (i.hom.left).toShHom ≅
        upperShriekCoherentPlus (i ≫ f) (comp i f C.P_g C.P_bar)
            C.A_fg.right C.A_fg.adjunction C.A_fg.plus C.A_fg.compatibility ⋙
          Plus.CohomologyIn.ambient
            (SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf))
    {p q :
      (Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])ᵒᵖ ×
        Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf]}
    (a : p ⟶ q) :
    (boundedShriekHom f C.P_g C.A_g).map a ≫
        shriekRestrictionHomApp i f C shriekRestrictionIso q.1.unop q.2 =
      shriekRestrictionHomApp i f C shriekRestrictionIso p.1.unop p.2 ≫
        ((restriction_open i).op.prod (𝟭 _) ⋙
          boundedShriekHom (i ≫ f) (comp i f C.P_g C.P_bar) C.A_fg).map a := sorry

/-- The Hom-bifunctor transformation obtained from the upper-shriek restriction
bridge. -/
noncomputable def shriekRestrictionHom (i : U ⟶ X) [IsOpenImmersion i.hom.left]
    (f : X ⟶ Y) (C : UpperShriekCompChoice i f)
    (shriekRestrictionIso :
      (upperShriekCoherentPlus f C.P_g C.A_g.right C.A_g.adjunction
          C.A_g.plus C.A_g.compatibility ⋙ Plus.CohomologyIn.ambient
            (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf)) ⋙
          RingedSpace.modulePullbackDerived (i.hom.left).toShHom ≅
        upperShriekCoherentPlus (i ≫ f) (comp i f C.P_g C.P_bar)
            C.A_fg.right C.A_fg.adjunction C.A_fg.plus C.A_fg.compatibility ⋙
          Plus.CohomologyIn.ambient
            (SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf)) :
    boundedShriekHom f C.P_g C.A_g ⟶
      (restriction_open i).op.prod (𝟭 _) ⋙
        boundedShriekHom (i ≫ f) (comp i f C.P_g C.P_bar) C.A_fg where
  app p := shriekRestrictionHomApp i f C shriekRestrictionIso p.1.unop p.2
  naturality _ _ a := shriekRestrictionHom_naturality i f C shriekRestrictionIso a

/-- The component of `shriekRestrictionHom` is its explicit upper-shriek restriction
chain. -/
theorem shriekRestrictionHom_app (i : U ⟶ X) [IsOpenImmersion i.hom.left]
    (f : X ⟶ Y) (C : UpperShriekCompChoice i f)
    (shriekRestrictionIso :
      (upperShriekCoherentPlus f C.P_g C.A_g.right C.A_g.adjunction
          C.A_g.plus C.A_g.compatibility ⋙ Plus.CohomologyIn.ambient
            (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf)) ⋙
          RingedSpace.modulePullbackDerived (i.hom.left).toShHom ≅
        upperShriekCoherentPlus (i ≫ f) (comp i f C.P_g C.P_bar)
            C.A_fg.right C.A_fg.adjunction C.A_fg.plus C.A_fg.compatibility ⋙
          Plus.CohomologyIn.ambient
            (SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf))
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])
    (L : Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf]) :
    (shriekRestrictionHom i f C shriekRestrictionIso).app (Opposite.op K, L) =
      shriekRestrictionHomApp i f C shriekRestrictionIso K L := sorry

/-- The coherent upper-shriek model becomes the defining quasicoherent upper-shriek
model after applying the canonical coherent-to-quasicoherent inclusion. -/
noncomputable def upperShriekCoherentInclusionIso (f : X ⟶ Y)
    (P : Scheme.Compactification.Of (Over.left Y.obj) (Over.mk f.hom.left))
    (A : Scheme.DerivedQCoh.PlusRightAdjoint (ambientMorphism P)) :
    upperShriekCoherentPlus f P A.right A.adjunction A.plus A.compatibility ⋙
        DerivedQCoh.coherentPlusInclusion (Over.left X.obj) ≅
      DerivedQCoh.coherentPlusInclusion (Over.left Y.obj) ⋙
        upperShriek f P A.plus :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ sorry)

/-- The upper-shriek compositor on bounded coherent models, obtained from
`UpperShriekCompChoice.compIso` through the canonical coherent inclusions. -/
noncomputable def upperShriekCoherentCompIso (i : U ⟶ X) (f : X ⟶ Y)
    (C : UpperShriekCompChoice i f) :
    upperShriekCoherentPlus (i ≫ f) (comp i f C.P_g C.P_bar)
        C.A_fg.right C.A_fg.adjunction C.A_fg.plus C.A_fg.compatibility ≅
      upperShriekCoherentPlus f C.P_g C.A_g.right C.A_g.adjunction
          C.A_g.plus C.A_g.compatibility ⋙
        upperShriekCoherentPlus i C.P_f C.A_f.right C.A_f.adjunction
          C.A_f.plus C.A_f.compatibility :=
  let hInclusion :
      (DerivedQCoh.coherentPlusInclusion (Over.left U.obj)).FullyFaithful := {
    preimage a := ObjectProperty.homMk a.hom
    map_preimage _ := sorry
    preimage_map _ := sorry }
  (hInclusion.whiskeringRight _).preimageIso
    (upperShriekCoherentInclusionIso (i ≫ f) (comp i f C.P_g C.P_bar) C.A_fg ≪≫
      Functor.isoWhiskerLeft (DerivedQCoh.coherentPlusInclusion (Over.left Y.obj))
        (C.compIso i f) ≪≫
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft
          (upperShriekCoherentPlus f C.P_g C.A_g.right C.A_g.adjunction
            C.A_g.plus C.A_g.compatibility)
          (upperShriekCoherentInclusionIso i C.P_f C.A_f) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (upperShriekCoherentInclusionIso f C.P_g C.A_g)
          (upperShriek i C.P_f C.A_f.plus) ≪≫
        Functor.associator _ _ _).symm)

/-- The canonical direct-to-iterated represented-Hom isomorphism induced by
`UpperShriekCompChoice.compIso`. -/
noncomputable def shriekCompositionIso (i : U ⟶ X) (f : X ⟶ Y)
    (C : UpperShriekCompChoice i f) :
    compositeShriekHom i f C ≅ iteratedShriekHom i f C :=
  NatIso.ofComponents
    (fun p ↦ (Iso.homCongr
      (Iso.refl ((Bounded.CohomologyIn.ambient
        (SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf)).obj p.1.unop))
      ((Plus.CohomologyIn.ambient
        (SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf)).mapIso
        ((upperShriekCoherentCompIso i f C).app
          ((boundedToPlus (Over.left Y.obj)).obj p.2)))).toIso)
    (fun _ ↦ sorry)

/-- A coherent compact-support restriction model consists of the two compact-support
functors, their represented-Hom comparisons, and the upper-shriek restriction bridge. -/
structure RestrictionModel (i : U ⟶ X) [IsOpenImmersion i.hom.left]
    (f : X ⟶ Y) (C : UpperShriekCompChoice i f) where
  pushforward : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf] ⥤
    Pro Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf]
  restrictedPushforward :
    Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf] ⥤
      Pro Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf]
  pushforwardComparison : Pro.representedHom pushforward ≅
    boundedShriekHom f C.P_g C.A_g
  restrictedComparison : Pro.representedHom restrictedPushforward ≅
    boundedShriekHom (i ≫ f) (comp i f C.P_g C.P_bar) C.A_fg
  shriekRestrictionIso :
    (upperShriekCoherentPlus f C.P_g C.A_g.right C.A_g.adjunction
        C.A_g.plus C.A_g.compatibility ⋙ Plus.CohomologyIn.ambient
          (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf)) ⋙
        RingedSpace.modulePullbackDerived (i.hom.left).toShHom ≅
      upperShriekCoherentPlus (i ≫ f) (comp i f C.P_g C.P_bar)
          C.A_fg.right C.A_fg.adjunction C.A_fg.plus C.A_fg.compatibility ⋙
        Plus.CohomologyIn.ambient
          (SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf)

namespace RestrictionModel

/-- Construct a restriction model from explicit represented-Hom comparisons and an
upper-shriek restriction bridge. -/
noncomputable def ofComparisons (i : U ⟶ X) [IsOpenImmersion i.hom.left]
    (f : X ⟶ Y) (C : UpperShriekCompChoice i f)
    (Rf : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf] ⥤
      Pro Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf])
    (Rg : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf] ⥤
      Pro Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf])
    (RfComparison : Pro.representedHom Rf ≅ boundedShriekHom f C.P_g C.A_g)
    (RgComparison : Pro.representedHom Rg ≅
      boundedShriekHom (i ≫ f) (comp i f C.P_g C.P_bar) C.A_fg)
    (shriekRestrictionIso :
      (upperShriekCoherentPlus f C.P_g C.A_g.right C.A_g.adjunction
          C.A_g.plus C.A_g.compatibility ⋙ Plus.CohomologyIn.ambient
            (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf)) ⋙
          RingedSpace.modulePullbackDerived (i.hom.left).toShHom ≅
        upperShriekCoherentPlus (i ≫ f) (comp i f C.P_g C.P_bar)
            C.A_fg.right C.A_fg.adjunction C.A_fg.plus C.A_fg.compatibility ⋙
          Plus.CohomologyIn.ambient
            (SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf)) :
    RestrictionModel i f C where
  pushforward := Rf
  restrictedPushforward := Rg
  pushforwardComparison := RfComparison
  restrictedComparison := RgComparison
  shriekRestrictionIso := shriekRestrictionIso

/-- The represented-Hom transformation encoded by a compact-support restriction
model. -/
noncomputable def homComparison {i : U ⟶ X} [IsOpenImmersion i.hom.left]
    {f : X ⟶ Y} {C : UpperShriekCompChoice i f}
    (M : RestrictionModel i f C) :
    Pro.representedHom M.pushforward ⟶
      Pro.representedHom
        (restriction_open i ⋙ M.restrictedPushforward) :=
  M.pushforwardComparison.hom ≫ shriekRestrictionHom i f C M.shriekRestrictionIso ≫
    Functor.whiskerLeft ((restriction_open i).op.prod (𝟭 _))
      M.restrictedComparison.inv ≫
    (Pro.representedHomPrecompIso
      (restriction_open i) M.restrictedPushforward).inv

/-- The represented-Hom comparison of a restriction model is the composite through
its two upper-shriek identifications. -/
theorem homComparison_def {i : U ⟶ X} [IsOpenImmersion i.hom.left]
    {f : X ⟶ Y} {C : UpperShriekCompChoice i f}
    (M : RestrictionModel i f C) :
    M.homComparison =
      M.pushforwardComparison.hom ≫ shriekRestrictionHom i f C M.shriekRestrictionIso ≫
        Functor.whiskerLeft ((restriction_open i).op.prod (𝟭 _))
          M.restrictedComparison.inv ≫
        (Pro.representedHomPrecompIso
          (restriction_open i) M.restrictedPushforward).inv := sorry

/-- The canonical restriction transformation recovered from the represented-Hom
comparison of a restriction model. -/
noncomputable def comparison {i : U ⟶ X} [IsOpenImmersion i.hom.left]
    {f : X ⟶ Y} {C : UpperShriekCompChoice i f}
    (M : RestrictionModel i f C) :
    restriction_open i ⋙ M.restrictedPushforward ⟶
      M.pushforward :=
  (Pro.representedHomNatTransEquiv _ _).symm M.homComparison

/-- Applying represented Hom to `RestrictionModel.comparison` recovers the model's
canonical Hom comparison. -/
theorem comparison_homComparison {i : U ⟶ X} [IsOpenImmersion i.hom.left]
    {f : X ⟶ Y} {C : UpperShriekCompChoice i f}
    (M : RestrictionModel i f C) :
    Pro.representedHomNatTransEquiv
        (restriction_open i ⋙ M.restrictedPushforward)
        M.pushforward M.comparison = M.homComparison := sorry

end RestrictionModel

/-- A Pro-extension of the proper pushforward belonging to a compactification,
together with its compatibility with stagewise bounded proper pushforward. -/
structure ProperPushforwardModel (f : X ⟶ Y)
    (P : Scheme.Compactification.Of (Over.left Y.obj) (Over.mk f.hom.left)) where
  functor :
    Pro Dᵇ[SheafOfModules.isCoherent (Over.left P.obj.right).ringCatSheaf] ⥤
      Pro Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf]
  presentationIso :
    (@Pro.lim Dᵇ[SheafOfModules.isCoherent (Over.left P.obj.right).ringCatSheaf] _
        (OrderDual ℕ+) _ _ _ _ ⋙ functor) ≅
      ((Functor.whiskeringRight (OrderDual ℕ+)
          Dᵇ[SheafOfModules.isCoherent (Over.left P.obj.right).ringCatSheaf]
          Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf]).obj
            (Scheme.ModuleDerived.properPushforward (Over.hom (Under.right P.obj))) ⋙
        @Pro.lim Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf] _
          (OrderDual ℕ+) _ _ _ _)

namespace ProperPushforwardModel

/-- Construct a Pro proper-pushforward model from a functor and its stagewise
proper-pushforward comparison. -/
noncomputable def ofPresentation (f : X ⟶ Y)
    (P : Scheme.Compactification.Of (Over.left Y.obj) (Over.mk f.hom.left))
    (functor :
      Pro Dᵇ[SheafOfModules.isCoherent (Over.left P.obj.right).ringCatSheaf] ⥤
        Pro Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf])
    (presentationIso :
      (@Pro.lim Dᵇ[SheafOfModules.isCoherent (Over.left P.obj.right).ringCatSheaf] _
          (OrderDual ℕ+) _ _ _ _ ⋙ functor) ≅
        ((Functor.whiskeringRight (OrderDual ℕ+)
            Dᵇ[SheafOfModules.isCoherent (Over.left P.obj.right).ringCatSheaf]
            Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf]).obj
              (Scheme.ModuleDerived.properPushforward (Over.hom (Under.right P.obj))) ⋙
          @Pro.lim Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf] _
            (OrderDual ℕ+) _ _ _ _)) :
    ProperPushforwardModel f P where
  functor := functor
  presentationIso := presentationIso

end ProperPushforwardModel

/-- Proper pushforward of the canonical extension-by-zero restriction map for a
fixed compactification. -/
noncomputable def fixedCompactificationComparison
    (i : U ⟶ X) [IsOpenImmersion i.hom.left] (f : X ⟶ Y)
    (P : Scheme.Compactification.Of (Over.left Y.obj) (Over.mk f.hom.left))
    (proper : ProperPushforwardModel f P) :
    restriction_open i ⋙
        (extensionByZero_comp_ι i f P ⋙ proper.functor) ⟶
      extensionByZero_ι f P ⋙ proper.functor :=
  (Functor.associator _ _ _).inv ≫ Functor.whiskerRight
    (@DeligneSystem.extensionByZeroRestriction _ _ _ i.hom.left (ι P)
        inferInstance (isNoetherian_mkHomLeft f)
        (isNoetherian_compactification f P) inferInstance
        (Scheme.Compactification.Of.instIsOpenImmersion _ _ P)) proper.functor

/-- The fixed-compactification comparison applies the proper-pushforward model to
the extension-by-zero restriction map. -/
theorem fixedCompactificationComparison_app
    (i : U ⟶ X) [IsOpenImmersion i.hom.left] (f : X ⟶ Y)
    (P : Scheme.Compactification.Of (Over.left Y.obj) (Over.mk f.hom.left))
    (proper : ProperPushforwardModel f P)
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf]) :
    (fixedCompactificationComparison i f P proper).app K =
      proper.functor.map
        ((@DeligneSystem.extensionByZeroRestriction _ _ _ i.hom.left (ι P)
        inferInstance (isNoetherian_mkHomLeft f)
        (isNoetherian_compactification f P) inferInstance
        (Scheme.Compactification.Of.instIsOpenImmersion _ _ P)).app K) := sorry

/-- The represented-Hom map induced by applying a Pro-pushforward model to an
extension-by-zero restriction comparison. -/
noncomputable def compositionRestrictionHomComparison
    (i : U ⟶ X) [IsOpenImmersion i.hom.left]
    (Ri : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf] ⥤
      Pro Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])
    (R : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf] ⥤
      Pro Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])
    (Rf : Pro Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf] ⥤
      Pro Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf])
    (extensionComparison :
      restriction_open i ⋙ Ri ⟶ R) :
    Pro.representedHom (R ⋙ Rf) ⟶
      Pro.representedHom
        (restriction_open i ⋙ (Ri ⋙ Rf)) :=
  Pro.representedHomNatTransEquiv
    (restriction_open i ⋙ (Ri ⋙ Rf))
    (R ⋙ Rf)
    ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight extensionComparison Rf)

/-- `compositionRestrictionHomComparison` is represented Hom applied to the
whiskered extension-by-zero restriction comparison. -/
theorem compositionRestrictionHomComparison_def
    (i : U ⟶ X) [IsOpenImmersion i.hom.left]
    (Ri : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf] ⥤
      Pro Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])
    (R : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf] ⥤
      Pro Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])
    (Rf : Pro Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf] ⥤
      Pro Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf])
    (extensionComparison :
      restriction_open i ⋙ Ri ⟶ R) :
    compositionRestrictionHomComparison i Ri R Rf extensionComparison =
      Pro.representedHomNatTransEquiv
        (restriction_open i ⋙ (Ri ⋙ Rf))
        (R ⋙ Rf)
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight extensionComparison Rf) := sorry

/-- The represented-Hom map induced by proper pushforward of the canonical
extension-by-zero restriction comparison for a fixed compactification. -/
noncomputable def fixedCompactificationHomComparison
    (i : U ⟶ X) [IsOpenImmersion i.hom.left] (f : X ⟶ Y)
    (P : Scheme.Compactification.Of (Over.left Y.obj) (Over.mk f.hom.left))
    (proper : ProperPushforwardModel f P) :
    Pro.representedHom
        (extensionByZero_ι f P ⋙ proper.functor) ⟶
      Pro.representedHom
        (restriction_open i ⋙
          (extensionByZero_comp_ι i f P ⋙ proper.functor)) :=
  Pro.representedHomNatTransEquiv
    (restriction_open i ⋙
      (extensionByZero_comp_ι i f P ⋙ proper.functor))
    (extensionByZero_ι f P ⋙ proper.functor)
    (fixedCompactificationComparison i f P proper)

/-- `fixedCompactificationHomComparison` is represented Hom applied to proper
pushforward of the canonical extension-by-zero restriction map. -/
theorem fixedCompactificationHomComparison_def
    (i : U ⟶ X) [IsOpenImmersion i.hom.left] (f : X ⟶ Y)
    (P : Scheme.Compactification.Of (Over.left Y.obj) (Over.mk f.hom.left))
    (proper : ProperPushforwardModel f P) :
    fixedCompactificationHomComparison i f P proper =
      Pro.representedHomNatTransEquiv
        (restriction_open i ⋙
          (extensionByZero_comp_ι i f P ⋙ proper.functor))
        (extensionByZero_ι f P ⋙ proper.functor)
        (fixedCompactificationComparison i f P proper) := sorry

namespace RestrictionModel

/-- The upper-shriek represented-Hom chain attached to a composition
presentation.  The compositor is inserted before transport back through the
iterated presentation. -/
noncomputable def compositionModelHomComparison {i : U ⟶ X}
    [IsOpenImmersion i.hom.left] {f : X ⟶ Y} {C : UpperShriekCompChoice i f}
    (M : RestrictionModel i f C)
    (Rf : Pro Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf] ⥤
      Pro Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf])
    (directRepresentation : Pro.representedHom
        (DeligneSystem.extensionByZero (𝟙 (Over.left X.obj)) ⋙ Rf) ≅
      boundedShriekHom f C.P_g C.A_g)
    (iteratedRepresentation : Pro.representedHom
        (DeligneSystem.extensionByZero
          (i.hom.left ≫ 𝟙 (Over.left X.obj)) ⋙ Rf) ≅
      iteratedShriekHom i f C) :
    Pro.representedHom
        (DeligneSystem.extensionByZero (𝟙 (Over.left X.obj)) ⋙ Rf) ⟶
      Pro.representedHom
        (restriction_open i ⋙
          (DeligneSystem.extensionByZero
            (i.hom.left ≫ 𝟙 (Over.left X.obj)) ⋙ Rf)) :=
  directRepresentation.hom ≫
    shriekRestrictionHom i f C M.shriekRestrictionIso ≫
    Functor.whiskerLeft
      ((restriction_open i).op.prod (𝟭 _))
      (shriekCompositionIso i f C).hom ≫
    Functor.whiskerLeft
      ((restriction_open i).op.prod (𝟭 _))
      iteratedRepresentation.inv ≫
    (Pro.representedHomPrecompIso
      (restriction_open i)
      (DeligneSystem.extensionByZero
        (i.hom.left ≫ 𝟙 (Over.left X.obj)) ⋙ Rf)).inv

/-- `compositionModelHomComparison` is the canonical upper-shriek restriction
chain transported through the composition presentation. -/
theorem compositionModelHomComparison_def {i : U ⟶ X}
    [IsOpenImmersion i.hom.left] {f : X ⟶ Y} {C : UpperShriekCompChoice i f}
    (M : RestrictionModel i f C)
    (Rf : Pro Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf] ⥤
      Pro Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf])
    (directRepresentation : Pro.representedHom
        (DeligneSystem.extensionByZero (𝟙 (Over.left X.obj)) ⋙ Rf) ≅
      boundedShriekHom f C.P_g C.A_g)
    (iteratedRepresentation : Pro.representedHom
        (DeligneSystem.extensionByZero
          (i.hom.left ≫ 𝟙 (Over.left X.obj)) ⋙ Rf) ≅
      iteratedShriekHom i f C) :
    compositionModelHomComparison M Rf directRepresentation iteratedRepresentation =
      directRepresentation.hom ≫
        shriekRestrictionHom i f C M.shriekRestrictionIso ≫
        Functor.whiskerLeft
          ((restriction_open i).op.prod (𝟭 _))
          (shriekCompositionIso i f C).hom ≫
        Functor.whiskerLeft
          ((restriction_open i).op.prod (𝟭 _))
          iteratedRepresentation.inv ≫
        (Pro.representedHomPrecompIso
          (restriction_open i)
          (DeligneSystem.extensionByZero
            (i.hom.left ≫ 𝟙 (Over.left X.obj)) ⋙ Rf)).inv := sorry

/-- Data expressing the first construction of the restriction arrow through an
actual `Riₗ!` model and a Pro-extension of `Rfₗ!`.  The represented-Hom
descriptions are derived from these functor-level comparisons and the canonical
comparisons of the restriction model, with coherence of the resulting arrow. -/
structure CompositionModel {i : U ⟶ X} [IsOpenImmersion i.hom.left]
    {f : X ⟶ Y} {C : UpperShriekCompChoice i f}
    (M : RestrictionModel i f C) where
  /-- The Pro-extension of the compact-support model for `f`. -/
  proPushforward :
    Pro Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf] ⥤
      Pro Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf]
  /-- The direct compact-support presentation of `M.pushforward`. -/
  directComparison :
    DeligneSystem.extensionByZero (𝟙 (Over.left X.obj)) ⋙ proPushforward ≅
      M.pushforward
  /-- The composition comparison for compactly supported pushforward from `M.restrictedPushforward` to the
  iterated compact-support presentation. -/
  lemmaComparison : M.restrictedPushforward ≅
    DeligneSystem.extensionByZero
      (i.hom.left ≫ 𝟙 (Over.left X.obj)) ⋙ proPushforward
  /-- The composition presentation carries the canonical restriction arrow
  determined by the represented-Hom restriction chain. -/
  comparisonCanonical :
    Functor.whiskerLeft (restriction_open i)
          lemmaComparison.hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (DeligneSystem.extensionByZeroRestriction i.hom.left
            (𝟙 (Over.left X.obj))) proPushforward ≫
        directComparison.hom =
      M.comparison

namespace CompositionModel

/-- Construct a composition model from a Pro-extended `Rfₗ!`, its direct and
iterated functor-level comparisons, and their canonicality coherence. -/
noncomputable def ofComparisons {i : U ⟶ X}
    [IsOpenImmersion i.hom.left] {f : X ⟶ Y} {C : UpperShriekCompChoice i f}
    (M : RestrictionModel i f C)
    (Rf : Pro Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf] ⥤
      Pro Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf])
    (directComparison :
      DeligneSystem.extensionByZero (𝟙 (Over.left X.obj)) ⋙ Rf ≅ M.pushforward)
    (lemmaComparison : M.restrictedPushforward ≅
      DeligneSystem.extensionByZero
        (i.hom.left ≫ 𝟙 (Over.left X.obj)) ⋙ Rf)
    (canonicality :
      Functor.whiskerLeft (restriction_open i)
            lemmaComparison.hom ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight
            (DeligneSystem.extensionByZeroRestriction i.hom.left
              (𝟙 (Over.left X.obj))) Rf ≫
          directComparison.hom =
        M.comparison) :
    CompositionModel M where
  proPushforward := Rf
  directComparison := directComparison
  lemmaComparison := lemmaComparison
  comparisonCanonical := canonicality

/-- Construct the composition presentation directly from its the represented Hom description of compactly supported pushforward
represented-Hom descriptions and the compact-support composition compositor. -/
noncomputable def ofRepresentations {i : U ⟶ X}
    [IsOpenImmersion i.hom.left] {f : X ⟶ Y} {C : UpperShriekCompChoice i f}
    (M : RestrictionModel i f C)
    (Rf : Pro Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf] ⥤
      Pro Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf])
    (directRepresentation : Pro.representedHom
        (DeligneSystem.extensionByZero (𝟙 (Over.left X.obj)) ⋙ Rf) ≅
      boundedShriekHom f C.P_g C.A_g)
    (iteratedRepresentation : Pro.representedHom
        (DeligneSystem.extensionByZero
          (i.hom.left ≫ 𝟙 (Over.left X.obj)) ⋙ Rf) ≅
      iteratedShriekHom i f C) :
    CompositionModel M where
  proPushforward := Rf
  directComparison := Pro.representedHomIsoOf _ _
    (M.pushforwardComparison ≪≫ directRepresentation.symm)
  lemmaComparison := Pro.representedHomIsoOf _ _
    (iteratedRepresentation ≪≫ (shriekCompositionIso i f C).symm ≪≫
      M.restrictedComparison.symm)
  comparisonCanonical := sorry

/-- The direct comparison of `ofRepresentations` is recovered faithfully from
the supplied direct represented-Hom presentation. -/
theorem ofRepresentations_directComparison {i : U ⟶ X}
    [IsOpenImmersion i.hom.left] {f : X ⟶ Y} {C : UpperShriekCompChoice i f}
    (M : RestrictionModel i f C)
    (Rf : Pro Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf] ⥤
      Pro Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf])
    (directRepresentation : Pro.representedHom
        (DeligneSystem.extensionByZero (𝟙 (Over.left X.obj)) ⋙ Rf) ≅
      boundedShriekHom f C.P_g C.A_g)
    (iteratedRepresentation : Pro.representedHom
        (DeligneSystem.extensionByZero
          (i.hom.left ≫ 𝟙 (Over.left X.obj)) ⋙ Rf) ≅
      iteratedShriekHom i f C) :
    (ofRepresentations M Rf directRepresentation
      iteratedRepresentation).directComparison =
        Pro.representedHomIsoOf _ _
          (M.pushforwardComparison ≪≫ directRepresentation.symm) := sorry

/-- The direct represented-Hom description, obtained from the represented Hom description of compactly supported pushforward
through the direct functor-level comparison. -/
noncomputable def directRepresentation {i : U ⟶ X}
    [IsOpenImmersion i.hom.left] {f : X ⟶ Y} {C : UpperShriekCompChoice i f}
    {M : RestrictionModel i f C} (N : CompositionModel M) :
    Pro.representedHom
        (DeligneSystem.extensionByZero (𝟙 (Over.left X.obj)) ⋙ N.proPushforward) ≅
      boundedShriekHom f C.P_g C.A_g :=
  (Pro.representedHomIsoMap _ _ N.directComparison).symm ≪≫
    M.pushforwardComparison

/-- The iterated represented-Hom description, obtained from the represented Hom description of compactly supported pushforward
and the canonical compact-support composition compositor. -/
noncomputable def iteratedRepresentation {i : U ⟶ X}
    [IsOpenImmersion i.hom.left] {f : X ⟶ Y} {C : UpperShriekCompChoice i f}
    {M : RestrictionModel i f C} (N : CompositionModel M) :
    Pro.representedHom
        (DeligneSystem.extensionByZero
          (i.hom.left ≫ 𝟙 (Over.left X.obj)) ⋙ N.proPushforward) ≅
      iteratedShriekHom i f C :=
  Pro.representedHomIsoMap _ _ N.lemmaComparison ≪≫
    M.restrictedComparison ≪≫ shriekCompositionIso i f C

/-- The represented-Hom image of `directComparison` is the canonical composite of
the two displayed representations. -/
theorem directComparison_spec {i : U ⟶ X} [IsOpenImmersion i.hom.left]
    {f : X ⟶ Y} {C : UpperShriekCompChoice i f}
    {M : RestrictionModel i f C} (N : CompositionModel M) :
    Pro.representedHomIsoMap
        (DeligneSystem.extensionByZero (𝟙 (Over.left X.obj)) ⋙ N.proPushforward)
        M.pushforward N.directComparison =
      M.pushforwardComparison ≪≫ N.directRepresentation.symm := sorry

/-- The represented-Hom image of `lemmaComparison` is the canonical composite
through `shriekCompositionIso`. -/
theorem lemmaComparison_spec {i : U ⟶ X} [IsOpenImmersion i.hom.left]
    {f : X ⟶ Y} {C : UpperShriekCompChoice i f}
    {M : RestrictionModel i f C} (N : CompositionModel M) :
    Pro.representedHomIsoMap M.restrictedPushforward
        (DeligneSystem.extensionByZero
          (i.hom.left ≫ 𝟙 (Over.left X.obj)) ⋙ N.proPushforward)
        N.lemmaComparison =
      N.iteratedRepresentation ≪≫ (shriekCompositionIso i f C).symm ≪≫
        M.restrictedComparison.symm := sorry

/-- The first restriction construction: use the composition isomorphism for compactly supported pushforward to pass
from `Rgₗ!` to `Rfₗ! ∘ Riₗ!`, then apply `Rfₗ!` to `Riₗ!(K|U) ⟶ K`. -/
noncomputable def comparison {i : U ⟶ X} [IsOpenImmersion i.hom.left]
    {f : X ⟶ Y} {C : UpperShriekCompChoice i f}
    {M : RestrictionModel i f C} (N : CompositionModel M) :
    restriction_open i ⋙ M.restrictedPushforward ⟶
      M.pushforward :=
    Functor.whiskerLeft (restriction_open i)
      N.lemmaComparison.hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (DeligneSystem.extensionByZeroRestriction i.hom.left
        (𝟙 (Over.left X.obj))) N.proPushforward ≫
    N.directComparison.hom

/-- The first construction factors through the explicit iterated compact-support
model and its composition comparison for compactly supported pushforward. -/
theorem comparison_def {i : U ⟶ X} [IsOpenImmersion i.hom.left]
    {f : X ⟶ Y} {C : UpperShriekCompChoice i f}
    {M : RestrictionModel i f C} (N : CompositionModel M) :
    N.comparison =
        Functor.whiskerLeft (restriction_open i)
          N.lemmaComparison.hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (DeligneSystem.extensionByZeroRestriction i.hom.left
            (𝟙 (Over.left X.obj))) N.proPushforward ≫
        N.directComparison.hom := sorry

/-- The construction through `Rfₗ! ∘ Riₗ!` is the canonical restriction
transformation obtained from represented Hom. -/
theorem comparison_eq {i : U ⟶ X} [IsOpenImmersion i.hom.left]
    {f : X ⟶ Y} {C : UpperShriekCompChoice i f}
    {M : RestrictionModel i f C} (N : CompositionModel M) :
    N.comparison = M.comparison := sorry

end CompositionModel

/-- The upper-shriek represented-Hom chain attached to a fixed compactification
presentation. -/
noncomputable def fixedCompactificationModelHomComparison
    {i : U ⟶ X} [IsOpenImmersion i.hom.left]
    {f : X ⟶ Y} {C : UpperShriekCompChoice i f}
    (M : RestrictionModel i f C)
    (P : Scheme.Compactification.Of (Over.left Y.obj) (Over.mk f.hom.left))
    (proper : ProperPushforwardModel f P)
    (pushforwardRepresentation : Pro.representedHom
        (extensionByZero_ι f P ⋙ proper.functor) ≅
      boundedShriekHom f C.P_g C.A_g)
    (restrictedRepresentation : Pro.representedHom
        (extensionByZero_comp_ι i f P ⋙ proper.functor) ≅
      boundedShriekHom (i ≫ f) (comp i f C.P_g C.P_bar) C.A_fg) :
    Pro.representedHom
        (extensionByZero_ι f P ⋙ proper.functor) ⟶
      Pro.representedHom
        (restriction_open i ⋙
          (extensionByZero_comp_ι i f P ⋙ proper.functor)) :=
  pushforwardRepresentation.hom ≫
    shriekRestrictionHom i f C M.shriekRestrictionIso ≫
    Functor.whiskerLeft
      ((restriction_open i).op.prod (𝟭 _))
      restrictedRepresentation.inv ≫
    (Pro.representedHomPrecompIso
      (restriction_open i)
      (extensionByZero_comp_ι i f P ⋙ proper.functor)).inv

/-- `fixedCompactificationModelHomComparison` is the canonical upper-shriek
restriction chain transported through the fixed-compactification presentation. -/
theorem fixedCompactificationModelHomComparison_def
    {i : U ⟶ X} [IsOpenImmersion i.hom.left]
    {f : X ⟶ Y} {C : UpperShriekCompChoice i f}
    (M : RestrictionModel i f C)
    (P : Scheme.Compactification.Of (Over.left Y.obj) (Over.mk f.hom.left))
    (proper : ProperPushforwardModel f P)
    (pushforwardRepresentation : Pro.representedHom
        (extensionByZero_ι f P ⋙ proper.functor) ≅
      boundedShriekHom f C.P_g C.A_g)
    (restrictedRepresentation : Pro.representedHom
        (extensionByZero_comp_ι i f P ⋙ proper.functor) ≅
      boundedShriekHom (i ≫ f) (comp i f C.P_g C.P_bar) C.A_fg) :
    fixedCompactificationModelHomComparison M P proper pushforwardRepresentation
        restrictedRepresentation =
      pushforwardRepresentation.hom ≫
        shriekRestrictionHom i f C M.shriekRestrictionIso ≫
        Functor.whiskerLeft
          ((restriction_open i).op.prod (𝟭 _))
          restrictedRepresentation.inv ≫
        (Pro.representedHomPrecompIso
          (restriction_open i)
          (extensionByZero_comp_ι i f P ⋙ proper.functor)).inv := sorry

/-- A fixed compactification realization of a restriction model.  Its
represented-Hom descriptions are derived from the two functor-level comparisons
and the canonical comparisons of the restriction model, with coherence of the
resulting arrow. -/
structure FixedCompactificationModel {i : U ⟶ X} [IsOpenImmersion i.hom.left]
    {f : X ⟶ Y} {C : UpperShriekCompChoice i f}
    (M : RestrictionModel i f C) where
  compactification :
    Scheme.Compactification.Of (Over.left Y.obj) (Over.mk f.hom.left)
  proper : ProperPushforwardModel f compactification
  /-- The comparison from the fixed `Rfₗ!` model to this compactification
  presentation. -/
  pushforwardComparison : M.pushforward ≅
    extensionByZero_ι f compactification ⋙ proper.functor
  /-- The comparison from the fixed `Rgₗ!` model to the restricted
  compactification presentation. -/
  restrictedComparison : M.restrictedPushforward ≅
    extensionByZero_comp_ι i f compactification ⋙ proper.functor
  /-- Proper pushforward of the extension-by-zero restriction arrow agrees with
  the canonical restriction transformation determined by represented Hom. -/
  comparisonCanonical :
    Functor.whiskerLeft (restriction_open i)
          restrictedComparison.hom ≫
        fixedCompactificationComparison i f compactification proper ≫
        pushforwardComparison.inv =
      M.comparison

namespace FixedCompactificationModel

/-- Construct a fixed compactification model from its compactification,
proper-pushforward model, functor-level comparisons, and canonicality coherence. -/
noncomputable def ofComparisons {i : U ⟶ X}
    [IsOpenImmersion i.hom.left] {f : X ⟶ Y} {C : UpperShriekCompChoice i f}
    (M : RestrictionModel i f C)
    (P : Scheme.Compactification.Of (Over.left Y.obj) (Over.mk f.hom.left))
    (proper : ProperPushforwardModel f P)
    (pushforwardComparison : M.pushforward ≅
      extensionByZero_ι f P ⋙ proper.functor)
    (restrictedComparison : M.restrictedPushforward ≅
      extensionByZero_comp_ι i f P ⋙ proper.functor)
    (canonicality :
      Functor.whiskerLeft (restriction_open i)
            restrictedComparison.hom ≫
          fixedCompactificationComparison i f P proper ≫
          pushforwardComparison.inv =
        M.comparison) :
    FixedCompactificationModel M where
  compactification := P
  proper := proper
  pushforwardComparison := pushforwardComparison
  restrictedComparison := restrictedComparison
  comparisonCanonical := canonicality

/-- Construct the fixed-compactification presentation directly from its two
the represented Hom description of compactly supported pushforward represented-Hom descriptions. -/
noncomputable def ofRepresentations {i : U ⟶ X}
    [IsOpenImmersion i.hom.left] {f : X ⟶ Y} {C : UpperShriekCompChoice i f}
    (M : RestrictionModel i f C)
    (P : Scheme.Compactification.Of (Over.left Y.obj) (Over.mk f.hom.left))
    (proper : ProperPushforwardModel f P)
    (pushforwardRepresentation : Pro.representedHom
        (extensionByZero_ι f P ⋙ proper.functor) ≅
      boundedShriekHom f C.P_g C.A_g)
    (restrictedRepresentation : Pro.representedHom
        (extensionByZero_comp_ι i f P ⋙ proper.functor) ≅
      boundedShriekHom (i ≫ f) (comp i f C.P_g C.P_bar) C.A_fg) :
    FixedCompactificationModel M where
  compactification := P
  proper := proper
  pushforwardComparison := Pro.representedHomIsoOf _ _
    (pushforwardRepresentation ≪≫ M.pushforwardComparison.symm)
  restrictedComparison := Pro.representedHomIsoOf _ _
    (restrictedRepresentation ≪≫ M.restrictedComparison.symm)
  comparisonCanonical := sorry

/-- The pushforward comparison of `ofRepresentations` is recovered faithfully
from the supplied fixed-compactification represented-Hom presentation. -/
theorem ofRepresentations_pushforwardComparison {i : U ⟶ X}
    [IsOpenImmersion i.hom.left] {f : X ⟶ Y} {C : UpperShriekCompChoice i f}
    (M : RestrictionModel i f C)
    (P : Scheme.Compactification.Of (Over.left Y.obj) (Over.mk f.hom.left))
    (proper : ProperPushforwardModel f P)
    (pushforwardRepresentation : Pro.representedHom
        (extensionByZero_ι f P ⋙ proper.functor) ≅
      boundedShriekHom f C.P_g C.A_g)
    (restrictedRepresentation : Pro.representedHom
        (extensionByZero_comp_ι i f P ⋙ proper.functor) ≅
      boundedShriekHom (i ≫ f) (comp i f C.P_g C.P_bar) C.A_fg) :
    (ofRepresentations M P proper pushforwardRepresentation
      restrictedRepresentation).pushforwardComparison =
        Pro.representedHomIsoOf _ _
          (pushforwardRepresentation ≪≫ M.pushforwardComparison.symm) := sorry

/-- The fixed-compactification representation of `Rfₗ!`, derived from Proposition
the represented Hom description of compactly supported pushforward through the fixed functor-level comparison. -/
noncomputable def pushforwardRepresentation {i : U ⟶ X}
    [IsOpenImmersion i.hom.left] {f : X ⟶ Y} {C : UpperShriekCompChoice i f}
    {M : RestrictionModel i f C} (N : FixedCompactificationModel M) :
    Pro.representedHom
        (extensionByZero_ι f N.compactification ⋙ N.proper.functor) ≅
      boundedShriekHom f C.P_g C.A_g :=
  Pro.representedHomIsoMap _ _ N.pushforwardComparison ≪≫
    M.pushforwardComparison

/-- The fixed-compactification representation of `Rgₗ!`, derived from Proposition
the represented Hom description of compactly supported pushforward through the restricted functor-level comparison. -/
noncomputable def restrictedRepresentation {i : U ⟶ X}
    [IsOpenImmersion i.hom.left] {f : X ⟶ Y} {C : UpperShriekCompChoice i f}
    {M : RestrictionModel i f C} (N : FixedCompactificationModel M) :
    Pro.representedHom
        (extensionByZero_comp_ι i f N.compactification ⋙ N.proper.functor) ≅
      boundedShriekHom (i ≫ f) (comp i f C.P_g C.P_bar) C.A_fg :=
  Pro.representedHomIsoMap _ _ N.restrictedComparison ≪≫
    M.restrictedComparison

/-- The represented-Hom image of `pushforwardComparison` is the canonical
composite of the compactification and restriction-model representations. -/
theorem pushforwardComparison_spec {i : U ⟶ X}
    [IsOpenImmersion i.hom.left] {f : X ⟶ Y} {C : UpperShriekCompChoice i f}
    {M : RestrictionModel i f C} (N : FixedCompactificationModel M) :
    Pro.representedHomIsoMap M.pushforward
        (extensionByZero_ι f N.compactification ⋙ N.proper.functor)
        N.pushforwardComparison =
      N.pushforwardRepresentation ≪≫ M.pushforwardComparison.symm := sorry

/-- The represented-Hom image of `restrictedComparison` is the canonical
composite of the compactification and restriction-model representations. -/
theorem restrictedComparison_spec {i : U ⟶ X}
    [IsOpenImmersion i.hom.left] {f : X ⟶ Y} {C : UpperShriekCompChoice i f}
    {M : RestrictionModel i f C} (N : FixedCompactificationModel M) :
    Pro.representedHomIsoMap M.restrictedPushforward
        (extensionByZero_comp_ι i f N.compactification ⋙ N.proper.functor)
        N.restrictedComparison =
      N.restrictedRepresentation ≪≫ M.restrictedComparison.symm := sorry

/-- The fixed-compactification restriction arrow transported to the functors of the
canonical restriction model. -/
noncomputable def comparison {i : U ⟶ X} [IsOpenImmersion i.hom.left]
    {f : X ⟶ Y} {C : UpperShriekCompChoice i f}
    {M : RestrictionModel i f C} (N : FixedCompactificationModel M) :
    restriction_open i ⋙ M.restrictedPushforward ⟶
      M.pushforward :=
  Functor.whiskerLeft (restriction_open i)
      N.restrictedComparison.hom ≫
    fixedCompactificationComparison i f N.compactification N.proper ≫
    N.pushforwardComparison.inv

/-- The fixed-compactification construction is proper pushforward of the
extension-by-zero restriction arrow, transported along the model comparisons. -/
theorem comparison_def {i : U ⟶ X} [IsOpenImmersion i.hom.left]
    {f : X ⟶ Y} {C : UpperShriekCompChoice i f}
    {M : RestrictionModel i f C} (N : FixedCompactificationModel M) :
    N.comparison =
      Functor.whiskerLeft (restriction_open i)
          N.restrictedComparison.hom ≫
        fixedCompactificationComparison i f N.compactification N.proper ≫
        N.pushforwardComparison.inv := sorry

/-- The construction using a fixed compactification is the canonical restriction
transformation obtained from represented Hom. -/
theorem comparison_eq {i : U ⟶ X} [IsOpenImmersion i.hom.left]
    {f : X ⟶ Y} {C : UpperShriekCompChoice i f}
    {M : RestrictionModel i f C} (N : FixedCompactificationModel M) :
    N.comparison = M.comparison := sorry

end FixedCompactificationModel


end RestrictionModel

/-- The three constructions of the open-restriction comparison of compactly supported
pushforwards agree: the represented Hom reconstruction, the composition construction,
and the construction using any fixed compactification. -/
theorem restrictionComparisons_eq {i : U ⟶ X} [IsOpenImmersion i.hom.left]
    {f : X ⟶ Y} {C : UpperShriekCompChoice i f}
    (M : RestrictionModel i f C) (composition : RestrictionModel.CompositionModel M)
    (compactification : RestrictionModel.FixedCompactificationModel M) :
    composition.comparison = M.comparison ∧
      compactification.comparison = M.comparison := sorry


end AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport
