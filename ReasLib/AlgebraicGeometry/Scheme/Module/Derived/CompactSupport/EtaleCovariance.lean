/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Etale.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.OpenRestriction

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

namespace EtaleCovariance

/-- A compact-support covariance model stores the two compactly supported
pushforwards, their represented-Hom descriptions, and the chosen étale
pullback-to-upper-shriek comparison. -/
structure Model (h : U ⟶ X) [AlgebraicGeometry.Etale h.hom.left]
    (f : X ⟶ Y) (C : UpperShriekCompChoice h f) where
  /-- The compactly supported pushforward along `f`. -/
  pushforward :
    Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf] ⥤
      Pro Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf]
  /-- The compactly supported pushforward along `h ≫ f`. -/
  compositePushforward :
    Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf] ⥤
      Pro Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf]
  /-- The represented-Hom description of compact support along `f`. -/
  pushforwardComparison : Pro.representedHom pushforward ≅
    boundedShriekHom f C.P_g C.A_g
  /-- The represented-Hom description of compact support along `h ≫ f`. -/
  compositeComparison : Pro.representedHom compositePushforward ≅
    boundedShriekHom (h ≫ f) (comp h f C.P_g C.P_bar) C.A_fg
  /-- The comparison `h^* f^! ≅ (h ≫ f)^!` on the chosen coherent
  upper-shriek models. -/
  shriekPullbackIso :
    (upperShriekCoherentPlus f C.P_g C.A_g.right C.A_g.adjunction
        C.A_g.plus C.A_g.compatibility ⋙ Plus.CohomologyIn.ambient
          (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf)) ⋙
        RingedSpace.modulePullbackDerived (h.hom.left).toShHom ≅
      upperShriekCoherentPlus (h ≫ f) (comp h f C.P_g C.P_bar)
          C.A_fg.right C.A_fg.adjunction C.A_fg.plus C.A_fg.compatibility ⋙
        Plus.CohomologyIn.ambient
          (SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf)

namespace Model

/-- Construct an étale covariance model from explicit compact-support and
upper-shriek comparisons. -/
noncomputable def ofComparisons (h : U ⟶ X)
    [AlgebraicGeometry.Etale h.hom.left] (f : X ⟶ Y)
    (C : UpperShriekCompChoice h f)
    (Rf : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf] ⥤
      Pro Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf])
    (Rhf : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf] ⥤
      Pro Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf])
    (RfComparison : Pro.representedHom Rf ≅ boundedShriekHom f C.P_g C.A_g)
    (RhfComparison : Pro.representedHom Rhf ≅
      boundedShriekHom (h ≫ f) (comp h f C.P_g C.P_bar) C.A_fg)
    (shriekPullbackIso :
      (upperShriekCoherentPlus f C.P_g C.A_g.right C.A_g.adjunction
          C.A_g.plus C.A_g.compatibility ⋙ Plus.CohomologyIn.ambient
            (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf)) ⋙
          RingedSpace.modulePullbackDerived (h.hom.left).toShHom ≅
        upperShriekCoherentPlus (h ≫ f) (comp h f C.P_g C.P_bar)
            C.A_fg.right C.A_fg.adjunction C.A_fg.plus C.A_fg.compatibility ⋙
          Plus.CohomologyIn.ambient
            (SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf)) :
    Model h f C where
  pushforward := Rf
  compositePushforward := Rhf
  pushforwardComparison := RfComparison
  compositeComparison := RhfComparison
  shriekPullbackIso := shriekPullbackIso

end Model

/-- The componentwise Hom map obtained by applying étale pullback and then the
chosen comparison `h^* f^! ≅ (h ≫ f)^!`. -/
noncomputable def shriekHomApp (h : U ⟶ X)
    [AlgebraicGeometry.Etale h.hom.left] (f : X ⟶ Y)
    (C : UpperShriekCompChoice h f) (M : Model h f C)
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])
    (L : Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf]) :
    (boundedShriekHom f C.P_g C.A_g).obj (Opposite.op K, L) ⟶
      (boundedShriekHom (h ≫ f) (comp h f C.P_g C.P_bar) C.A_fg).obj
        (Opposite.op ((ModuleDerived.Etale.pullback h.hom.left).obj K), L) :=
  ↾fun a ↦
    (ModuleDerived.Etale.pullbackAmbientIso h.hom.left).hom.app K ≫
      (RingedSpace.modulePullbackDerived (h.hom.left).toShHom).map a ≫
        (M.shriekPullbackIso.app ((boundedToPlus (Over.left Y.obj)).obj L)).hom

/-- Applying `shriekHomApp` is the displayed three-arrow Hom chain. -/
theorem shriekHomApp_apply (h : U ⟶ X)
    [AlgebraicGeometry.Etale h.hom.left] (f : X ⟶ Y)
    (C : UpperShriekCompChoice h f) (M : Model h f C)
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])
    (L : Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf])
    (a : (boundedShriekHom f C.P_g C.A_g).obj (Opposite.op K, L)) :
    shriekHomApp h f C M K L a =
      (ModuleDerived.Etale.pullbackAmbientIso h.hom.left).hom.app K ≫
        (RingedSpace.modulePullbackDerived (h.hom.left).toShHom).map a ≫
          (M.shriekPullbackIso.app
            ((boundedToPlus (Over.left Y.obj)).obj L)).hom := sorry

/-- The componentwise étale upper-shriek Hom chain is natural in both bounded
coherent variables. -/
theorem shriekHom_naturality (h : U ⟶ X)
    [AlgebraicGeometry.Etale h.hom.left] (f : X ⟶ Y)
    (C : UpperShriekCompChoice h f) (M : Model h f C)
    {p q :
      (Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])ᵒᵖ ×
        Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf]}
    (a : p ⟶ q) :
    (boundedShriekHom f C.P_g C.A_g).map a ≫
        shriekHomApp h f C M q.1.unop q.2 =
      shriekHomApp h f C M p.1.unop p.2 ≫
        ((ModuleDerived.Etale.pullback h.hom.left).op.prod (𝟭 _) ⋙
          boundedShriekHom (h ≫ f) (comp h f C.P_g C.P_bar) C.A_fg).map a := sorry

/-- The bifunctorial Hom transformation defined by étale pullback and the chosen
upper-shriek comparison. -/
noncomputable def shriekHom (h : U ⟶ X)
    [AlgebraicGeometry.Etale h.hom.left] (f : X ⟶ Y)
    (C : UpperShriekCompChoice h f) (M : Model h f C) :
    boundedShriekHom f C.P_g C.A_g ⟶
      (ModuleDerived.Etale.pullback h.hom.left).op.prod (𝟭 _) ⋙
        boundedShriekHom (h ≫ f) (comp h f C.P_g C.P_bar) C.A_fg where
  app p := shriekHomApp h f C M p.1.unop p.2
  naturality _ _ a := shriekHom_naturality h f C M a

/-- The component of `shriekHom` is the explicit étale upper-shriek Hom map. -/
theorem shriekHom_app (h : U ⟶ X)
    [AlgebraicGeometry.Etale h.hom.left] (f : X ⟶ Y)
    (C : UpperShriekCompChoice h f) (M : Model h f C)
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])
    (L : Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf]) :
    (shriekHom h f C M).app (Opposite.op K, L) = shriekHomApp h f C M K L := sorry

/-- The represented-Hom transformation determining étale covariance of compact
support. -/
noncomputable def homComparison {h : U ⟶ X}
    [AlgebraicGeometry.Etale h.hom.left] {f : X ⟶ Y}
    {C : UpperShriekCompChoice h f} (M : Model h f C) :
    Pro.representedHom M.pushforward ⟶
      Pro.representedHom
        (ModuleDerived.Etale.pullback h.hom.left ⋙ M.compositePushforward) :=
  M.pushforwardComparison.hom ≫ shriekHom h f C M ≫
    Functor.whiskerLeft
      ((ModuleDerived.Etale.pullback h.hom.left).op.prod (𝟭 _))
      M.compositeComparison.inv ≫
    (Pro.representedHomPrecompIso
      (ModuleDerived.Etale.pullback h.hom.left) M.compositePushforward).inv

/-- The represented-Hom comparison is the composite through the two compact-support
representations and the étale upper-shriek Hom chain. -/
theorem homComparison_def {h : U ⟶ X}
    [AlgebraicGeometry.Etale h.hom.left] {f : X ⟶ Y}
    {C : UpperShriekCompChoice h f} (M : Model h f C) :
    homComparison M = M.pushforwardComparison.hom ≫ shriekHom h f C M ≫
      Functor.whiskerLeft
        ((ModuleDerived.Etale.pullback h.hom.left).op.prod (𝟭 _))
        M.compositeComparison.inv ≫
      (Pro.representedHomPrecompIso
        (ModuleDerived.Etale.pullback h.hom.left) M.compositePushforward).inv := sorry

/-- For an étale morphism `h : U ⟶ X`, the canonical compact-support covariance
map is a natural transformation `R(h ≫ f)_! (h^* K) ⟶ Rf_! K`. -/
noncomputable def comparison {h : U ⟶ X}
    [AlgebraicGeometry.Etale h.hom.left] {f : X ⟶ Y}
    {C : UpperShriekCompChoice h f} (M : Model h f C) :
    ModuleDerived.Etale.pullback h.hom.left ⋙ M.compositePushforward ⟶
      M.pushforward :=
  (Pro.representedHomNatTransEquiv _ _).symm (homComparison M)

/-- Applying represented Hom to `comparison` recovers the defining étale
upper-shriek Hom transformation. -/
theorem comparison_homComparison {h : U ⟶ X}
    [AlgebraicGeometry.Etale h.hom.left] {f : X ⟶ Y}
    {C : UpperShriekCompChoice h f} (M : Model h f C) :
    Pro.representedHomNatTransEquiv
        (ModuleDerived.Etale.pullback h.hom.left ⋙ M.compositePushforward)
        M.pushforward (comparison M) = homComparison M := sorry

end EtaleCovariance

end CompactSupport

end ModuleDerived

end Scheme

end AlgebraicGeometry
