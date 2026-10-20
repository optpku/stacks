/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.MayerVietoris.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.EtaleBaseChange
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Identity
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Exact

/-! # Cochain and derived Mayer–Vietoris triangles for étale pushforward -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits
open CategoryTheory.Functor CategoryTheory.Pretriangulated ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- Identification `R(g_* ((-)|_W)) ≅ (-)|_W ⋙ Rg_*` of derived functors on `D(𝒪_X)`. -/
def mayerVietorisPushforwardDerivedIso {W X : AlgebraicSpace S} (g : W ⟶ X)
    [Etale g] :
    modulesHomotopyFunctor (restrictFunctor g ⋙ pushforward g) ≅
      restrictFunctorDerived g ⋙ moduleDerivedPushforward g :=
  asIso (derivedRestrictPushforwardComparison (h := g) (f' := g))

/-- The K-injective total right-derived functor of the identity on `𝒪_X`-modules is the
identity of `D(𝒪_X)`. -/
def mayerVietorisPushforwardDerivedIdIso (X : AlgebraicSpace S) :
    Functor.RightDerived.Homotopy.functor (𝟭 X.Modules) ≅ 𝟭 (ModuleDerived X) :=
  (Functor.RightDerived.Exact.homotopyIso (𝟭 X.Modules)).symm ≪≫
    ExactFunctor.MapDerivedCategory.idFunctorIso X.Modules

set_option backward.isDefEq.respectTransparency false in
/-- On a K-injective complex, the cochain-level unit of `g_* ((-)|_W)` is an isomorphism. -/
theorem isIso_mayerVietorisPushforward_composite_unit_app {W X : AlgebraicSpace S}
    (g : W ⟶ X) [Etale g]
    (K : CochainComplex X.Modules ℤ) [K.IsKInjective] :
    IsIso ((Functor.RightDerived.KInjective.unit.{u}
        (restrictFunctor g ⋙ pushforward g)).app K) :=
  by
    let F := restrictFunctor g ⋙ pushforward g
    let a : K ⟶ (CochainComplex.KInjectiveResolution.Construction.replacement.{u}
        X.Modules).obj K :=
      (CochainComplex.KInjectiveResolution.Construction.augmentation.{u} X.Modules).app K
    have hReplacement : ((CochainComplex.KInjectiveResolution.Construction.replacement.{u}
      X.Modules).obj K).IsKInjective :=
      CochainComplex.KInjectiveResolution.Construction.replacement_isKInjective X.Modules K
    have ha : QuasiIso a :=
      CochainComplex.KInjectiveResolution.Construction.augmentation_quasiIso X.Modules K
    have hq : IsIso ((HomotopyCategory.quotient X.Modules (up ℤ)).map a) :=
      HomotopyCategory.quotient_inverts_homotopyEquivalences _ _ a
        ((CochainComplex.IsKInjective.quasiIso_iff a).1 ha)
    have hm : IsIso (((HomotopyCategory.quotient X.Modules (up ℤ)) ⋙
      Functor.Homotopy.toDerived F).map a) := by
      change IsIso ((Functor.Homotopy.toDerived F).map
        ((HomotopyCategory.quotient X.Modules (up ℤ)).map a))
      infer_instance
    have hm' : IsIso ((Functor.KInjectiveModel.ordinaryCochain F).map a) :=
      (NatIso.isIso_map_iff (Functor.Homotopy.cochainIso F) a).1 hm
    have hunit : IsIso ((Functor.KInjectiveModel.unit.{u} F).app K) := by
      dsimp [Functor.KInjectiveModel.unit]
      change IsIso (𝟙 _ ≫ (Functor.KInjectiveModel.ordinaryCochain F).map a ≫ _)
      infer_instance
    -- The explicit certificate fixes the supplied cochain unit for native uniqueness.
    have hDerived : (Functor.RightDerived.KInjective.functor.{u} F).IsRightDerivedFunctor
        (Functor.RightDerived.KInjective.unit.{u} F)
        (HomologicalComplex.quasiIso X.Modules (up ℤ)) :=
      Functor.RightDerived.KInjective.isRightDerived F
    let e := Functor.KInjectiveModel.isoOfModel.{u} F
      (Functor.RightDerived.KInjective.functor.{u} F)
      (Functor.RightDerived.KInjective.unit.{u} F)
    have he : (Functor.KInjectiveModel.unit.{u} F).app K ≫
        e.hom.app (DerivedCategory.Q.obj K) =
        (Functor.RightDerived.KInjective.unit.{u} F).app K := by
      simpa [e, Functor.KInjectiveModel.isoOfModel, Functor.rightDerivedUnique,
        Functor.rightDerivedNatIso, Functor.rightDerivedNatTrans] using
        (Functor.KInjectiveModel.derived.{u} F).rightDerived_fac_app
          (Functor.KInjectiveModel.unit.{u} F)
          (HomologicalComplex.quasiIso X.Modules (up ℤ))
          (Functor.RightDerived.KInjective.functor.{u} F)
          (𝟙 _ ≫ Functor.RightDerived.KInjective.unit.{u} F) K
    rw [← he]
    infer_instance

variable {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]

/-- The cochain-level first Mayer–Vietoris arrow. -/
def mayerVietorisPushforwardCochainι (K : CochainComplex X.Modules ℤ) :
    K ⟶
      biprod (((restrictFunctor j ⋙ pushforward j).mapHomologicalComplex (up ℤ)).obj K)
        (((restrictFunctor f ⋙ pushforward f).mapHomologicalComplex (up ℤ)).obj K) :=
  biprod.lift
    ((Functor.mapHomologicalComplexIdIso X.Modules (up ℤ)).inv.app K ≫
      (NatTrans.mapHomologicalComplex (mayerVietorisPushforwardιNatTransU j) (up ℤ)).app K)
    ((Functor.mapHomologicalComplexIdIso X.Modules (up ℤ)).inv.app K ≫
      (NatTrans.mapHomologicalComplex (mayerVietorisPushforwardιNatTransV f) (up ℤ)).app K)

/-- The cochain-level second Mayer–Vietoris arrow. -/
def mayerVietorisPushforwardCochainπ (K : CochainComplex X.Modules ℤ) :
    biprod (((restrictFunctor j ⋙ pushforward j).mapHomologicalComplex (up ℤ)).obj K)
        (((restrictFunctor f ⋙ pushforward f).mapHomologicalComplex (up ℤ)).obj K) ⟶
      ((restrictFunctor (fiberHom j f) ⋙ pushforward (fiberHom j f)).mapHomologicalComplex
        (up ℤ)).obj K :=
  biprod.desc
    ((NatTrans.mapHomologicalComplex (mayerVietorisPushforwardπNatTransU j f) (up ℤ)).app K)
    (-(NatTrans.mapHomologicalComplex (mayerVietorisPushforwardπNatTransV j f) (up ℤ)).app K)

/-- The degreewise diagonal unit followed by the difference of overlap restrictions is zero. -/
theorem mayerVietorisPushforwardCochain_ι_comp_π (K : CochainComplex X.Modules ℤ) :
    mayerVietorisPushforwardCochainι j f K ≫ mayerVietorisPushforwardCochainπ j f K = 0 :=
  sorry

/-- The short complex of cochain complexes obtained by applying the module-level
Mayer–Vietoris arrows degreewise. -/
def mayerVietorisPushforwardCochainShortComplex (K : CochainComplex X.Modules ℤ) :
    ShortComplex (CochainComplex X.Modules ℤ) :=
  ShortComplex.mk (mayerVietorisPushforwardCochainι j f K)
    (mayerVietorisPushforwardCochainπ j f K)
    (mayerVietorisPushforwardCochain_ι_comp_π j f K)

/-- Derived `U`-leg unit in `D(𝒪_X)`. -/
def mayerVietorisPushforwardιDerivedU (E : ModuleDerived X) :
    E ⟶ (moduleDerivedPushforward j).obj ((restrictFunctorDerived j).obj E) :=
  (mayerVietorisPushforwardDerivedIdIso X).inv.app E ≫
    (Functor.RightDerived.Homotopy.mapNatTrans
      (mayerVietorisPushforwardιNatTransU j)).app E ≫
    (mayerVietorisPushforwardDerivedIso j).hom.app E

/-- Derived `V`-leg unit in `D(𝒪_X)`. -/
def mayerVietorisPushforwardιDerivedV (E : ModuleDerived X) :
    E ⟶ (moduleDerivedPushforward f).obj ((restrictFunctorDerived f).obj E) :=
  (mayerVietorisPushforwardDerivedIdIso X).inv.app E ≫
    (Functor.RightDerived.Homotopy.mapNatTrans
      (mayerVietorisPushforwardιNatTransV f)).app E ≫
    (mayerVietorisPushforwardDerivedIso f).hom.app E

/-- Derived first Mayer–Vietoris arrow in `D(𝒪_X)`. -/
def mayerVietorisPushforwardιDerived (E : ModuleDerived X) :
    E ⟶
      biprod ((moduleDerivedPushforward j).obj ((restrictFunctorDerived j).obj E))
        ((moduleDerivedPushforward f).obj ((restrictFunctorDerived f).obj E)) :=
  biprod.lift (mayerVietorisPushforwardιDerivedU j E)
    (mayerVietorisPushforwardιDerivedV f E)

/-- Derived `U`-leg overlap restriction in `D(𝒪_X)`. -/
def mayerVietorisPushforwardπDerivedU (E : ModuleDerived X) :
    (moduleDerivedPushforward j).obj ((restrictFunctorDerived j).obj E) ⟶
      (moduleDerivedPushforward (fiberHom j f)).obj
        ((restrictFunctorDerived (fiberHom j f)).obj E) :=
  (mayerVietorisPushforwardDerivedIso j).inv.app E ≫
    (Functor.RightDerived.Homotopy.mapNatTrans
      (mayerVietorisPushforwardπNatTransU j f)).app E ≫
    (mayerVietorisPushforwardDerivedIso (fiberHom j f)).hom.app E

/-- Derived `V`-leg overlap restriction in `D(𝒪_X)`. -/
def mayerVietorisPushforwardπDerivedV (E : ModuleDerived X) :
    (moduleDerivedPushforward f).obj ((restrictFunctorDerived f).obj E) ⟶
      (moduleDerivedPushforward (fiberHom j f)).obj
        ((restrictFunctorDerived (fiberHom j f)).obj E) :=
  (mayerVietorisPushforwardDerivedIso f).inv.app E ≫
    (Functor.RightDerived.Homotopy.mapNatTrans
      (mayerVietorisPushforwardπNatTransV j f)).app E ≫
    (mayerVietorisPushforwardDerivedIso (fiberHom j f)).hom.app E

/-- Derived second Mayer–Vietoris arrow in `D(𝒪_X)`. -/
def mayerVietorisPushforwardπDerived (E : ModuleDerived X) :
    biprod ((moduleDerivedPushforward j).obj ((restrictFunctorDerived j).obj E))
        ((moduleDerivedPushforward f).obj ((restrictFunctorDerived f).obj E)) ⟶
      (moduleDerivedPushforward (fiberHom j f)).obj
        ((restrictFunctorDerived (fiberHom j f)).obj E) :=
  biprod.desc (mayerVietorisPushforwardπDerivedU j f E)
    (-mayerVietorisPushforwardπDerivedV j f E)

variable [IsElementaryDistinguishedSquare j f]

/-- The cochain-level Mayer–Vietoris sequence is short exact. -/
theorem mayerVietorisPushforwardCochain_shortExact (K : CochainComplex X.Modules ℤ) :
    (mayerVietorisPushforwardCochainShortComplex j f K).ShortExact :=
  sorry

/-- The connecting maps of the degreewise short exact sequences commute with cochain maps. -/
theorem mayerVietorisPushforwardδCochain_naturality
    {K L : CochainComplex X.Modules ℤ} (φ : K ⟶ L) :
    ((restrictFunctor (fiberHom j f) ⋙ pushforward (fiberHom j f)).mapHomologicalComplex
        (up ℤ) ⋙ DerivedCategory.Q).map φ ≫
        DerivedCategory.triangleOfSESδ (mayerVietorisPushforwardCochain_shortExact j f L) =
      DerivedCategory.triangleOfSESδ (mayerVietorisPushforwardCochain_shortExact j f K) ≫
        (DerivedCategory.Q ⋙ shiftFunctor (ModuleDerived X) (1 : ℤ)).map φ :=
  sorry

/-- Cochain-level connecting maps of the Mayer–Vietoris short exact sequences, as a natural
transformation `g_* ((-)|_W) ⋙ Q ⟶ Q ⋙ ((-)⟦1⟧)` along the overlap morphism. -/
def mayerVietorisPushforwardδCochain :
    (restrictFunctor (fiberHom j f) ⋙ pushforward (fiberHom j f)).mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ ModuleDerived X) ⟶
      (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ ModuleDerived X) ⋙
        shiftFunctor (ModuleDerived X) (1 : ℤ) where
  app K := DerivedCategory.triangleOfSESδ (mayerVietorisPushforwardCochain_shortExact j f K)
  naturality := fun _ _ φ ↦ mayerVietorisPushforwardδCochain_naturality j f φ

/-- Connecting morphism of derived functors, obtained by descending the cochain-level
`triangleOfSESδ` along the K-injective unit of the overlap composite. -/
def mayerVietorisPushforwardδNatTrans :
    Functor.RightDerived.Homotopy.functor
        (restrictFunctor (fiberHom j f) ⋙ pushforward (fiberHom j f)) ⟶
      shiftFunctor (ModuleDerived X) (1 : ℤ) :=
  Functor.RightDerived.Homotopy.cochainExtensionDesc
    (restrictFunctor (fiberHom j f) ⋙ pushforward (fiberHom j f))
    (shiftFunctor (ModuleDerived X) (1 : ℤ))
    (mayerVietorisPushforwardδCochain j f)

/-- The connecting morphism of the Mayer–Vietoris triangle in `D(𝒪_X)`. -/
def mayerVietorisPushforwardδ (E : ModuleDerived X) :
    (moduleDerivedPushforward (fiberHom j f)).obj
      ((restrictFunctorDerived (fiberHom j f)).obj E) ⟶ E⟦(1 : ℤ)⟧ :=
  (mayerVietorisPushforwardDerivedIso (fiberHom j f)).inv.app E ≫
    (mayerVietorisPushforwardδNatTrans j f).app E

/-- The Mayer–Vietoris distinguished-triangle data of étale pushforward in `D(𝒪_X)`. -/
def mayerVietorisPushforwardTriangle (E : ModuleDerived X) :
    Triangle (ModuleDerived X) :=
  Triangle.mk (mayerVietorisPushforwardιDerived j f E)
    (mayerVietorisPushforwardπDerived j f E) (mayerVietorisPushforwardδ j f E)

/-- The first vertex of the Mayer–Vietoris triangle is `E`. -/
theorem mayerVietorisPushforwardTriangle_obj₁ (E : ModuleDerived X) :
    (mayerVietorisPushforwardTriangle j f E).obj₁ = E :=
  rfl

/-- The second vertex of the Mayer–Vietoris triangle is
`Rj_{U,*} (E|_U) ⊞ Rj_{V,*} (E|_V)`. -/
theorem mayerVietorisPushforwardTriangle_obj₂ (E : ModuleDerived X) :
    (mayerVietorisPushforwardTriangle j f E).obj₂ =
      biprod ((moduleDerivedPushforward j).obj ((restrictFunctorDerived j).obj E))
        ((moduleDerivedPushforward f).obj ((restrictFunctorDerived f).obj E)) :=
  rfl

/-- The third vertex of the Mayer–Vietoris triangle is
`Rj_{U×_X V,*} (E|_{U×_X V})`. -/
theorem mayerVietorisPushforwardTriangle_obj₃ (E : ModuleDerived X) :
    (mayerVietorisPushforwardTriangle j f E).obj₃ =
      (moduleDerivedPushforward (fiberHom j f)).obj
        ((restrictFunctorDerived (fiberHom j f)).obj E) :=
  rfl

/-- The canonical component identifications commute with all three arrows of the
Mayer–Vietoris triangle and the triangle of the cochain short exact sequence. -/
private theorem mayerVietorisPushforwardTriangle_eq_triangleOfSES_comm
    (K : CochainComplex X.Modules ℤ) [K.IsKInjective] [∀ n, Injective (K.X n)]
    (h : (mayerVietorisPushforwardCochainShortComplex j f K).ShortExact) :
  let T := mayerVietorisPushforwardTriangle j f (DerivedCategory.Q.obj K)
  let T' := DerivedCategory.triangleOfSES h
  let eW :=
    (mayerVietorisPushforwardDerivedIso (fiberHom j f)).symm.app (DerivedCategory.Q.obj K) ≪≫
      (@asIso _ _ _ _ ((Functor.RightDerived.KInjective.unit.{u}
        (restrictFunctor (fiberHom j f) ⋙ pushforward (fiberHom j f))).app K)
        (isIso_mayerVietorisPushforward_composite_unit_app (fiberHom j f) K)).symm
  let eU :=
    (mayerVietorisPushforwardDerivedIso j).symm.app (DerivedCategory.Q.obj K) ≪≫
      (@asIso _ _ _ _ ((Functor.RightDerived.KInjective.unit.{u}
        (restrictFunctor j ⋙ pushforward j)).app K)
        (isIso_mayerVietorisPushforward_composite_unit_app j K)).symm
  let eV :=
    (mayerVietorisPushforwardDerivedIso f).symm.app (DerivedCategory.Q.obj K) ≪≫
      (@asIso _ _ _ _ ((Functor.RightDerived.KInjective.unit.{u}
        (restrictFunctor f ⋙ pushforward f)).app K)
        (isIso_mayerVietorisPushforward_composite_unit_app f K)).symm
  let KU := ((restrictFunctor j ⋙ pushforward j).mapHomologicalComplex (up ℤ)).obj K
  let KV := ((restrictFunctor f ⋙ pushforward f).mapHomologicalComplex (up ℤ)).obj K
  let e₁ : T.obj₁ ≅ T'.obj₁ := Iso.refl _
  let e₂ : T.obj₂ ≅ T'.obj₂ :=
    biprod.mapIso eU eV ≪≫
      (@Functor.mapBiprod _ _ _ _ _ _ DerivedCategory.Q KU KV inferInstance inferInstance
        (preservesBinaryBiproduct_of_preservesBiproduct DerivedCategory.Q KU KV)).symm
  T.mor₁ ≫ e₂.hom = e₁.hom ≫ T'.mor₁ ∧
    T.mor₂ ≫ eW.hom = e₂.hom ≫ T'.mor₂ ∧
    T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧' = eW.hom ≫ T'.mor₃ :=
  sorry

/-- For a K-injective termwise-injective complex, the pushforward Mayer–Vietoris
triangle is canonically isomorphic to the triangle of its degreewise short exact sequence. -/
def mayerVietorisPushforwardTriangle_eq_triangleOfSES
    (K : CochainComplex X.Modules ℤ) [K.IsKInjective] [∀ n, Injective (K.X n)]
    (h : (mayerVietorisPushforwardCochainShortComplex j f K).ShortExact) :
    mayerVietorisPushforwardTriangle j f (DerivedCategory.Q.obj K) ≅
      DerivedCategory.triangleOfSES h :=
  let T := mayerVietorisPushforwardTriangle j f (DerivedCategory.Q.obj K)
  let T' := DerivedCategory.triangleOfSES h
  let eW :=
    (mayerVietorisPushforwardDerivedIso (fiberHom j f)).symm.app (DerivedCategory.Q.obj K) ≪≫
      (@asIso _ _ _ _ ((Functor.RightDerived.KInjective.unit.{u}
        (restrictFunctor (fiberHom j f) ⋙ pushforward (fiberHom j f))).app K)
        (isIso_mayerVietorisPushforward_composite_unit_app (fiberHom j f) K)).symm
  let eU :=
    (mayerVietorisPushforwardDerivedIso j).symm.app (DerivedCategory.Q.obj K) ≪≫
      (@asIso _ _ _ _ ((Functor.RightDerived.KInjective.unit.{u}
        (restrictFunctor j ⋙ pushforward j)).app K)
        (isIso_mayerVietorisPushforward_composite_unit_app j K)).symm
  let eV :=
    (mayerVietorisPushforwardDerivedIso f).symm.app (DerivedCategory.Q.obj K) ≪≫
      (@asIso _ _ _ _ ((Functor.RightDerived.KInjective.unit.{u}
        (restrictFunctor f ⋙ pushforward f)).app K)
        (isIso_mayerVietorisPushforward_composite_unit_app f K)).symm
  let KU := ((restrictFunctor j ⋙ pushforward j).mapHomologicalComplex (up ℤ)).obj K
  let KV := ((restrictFunctor f ⋙ pushforward f).mapHomologicalComplex (up ℤ)).obj K
  let e₁ : T.obj₁ ≅ T'.obj₁ := Iso.refl _
  let e₂ : T.obj₂ ≅ T'.obj₂ :=
    biprod.mapIso eU eV ≪≫
      (@Functor.mapBiprod _ _ _ _ _ _ DerivedCategory.Q KU KV inferInstance inferInstance
        (preservesBinaryBiproduct_of_preservesBiproduct DerivedCategory.Q KU KV)).symm
  Triangle.isoMk T T' e₁ e₂ eW
    (by exact (mayerVietorisPushforwardTriangle_eq_triangleOfSES_comm j f K h).1)
    (by exact (mayerVietorisPushforwardTriangle_eq_triangleOfSES_comm j f K h).2.1)
    (by exact (mayerVietorisPushforwardTriangle_eq_triangleOfSES_comm j f K h).2.2)

/-- The first component of the short-exact-sequence triangle comparison is the identity. -/
theorem mayerVietorisPushforwardTriangle_eq_triangleOfSES_hom₁
    (K : CochainComplex X.Modules ℤ) [K.IsKInjective] [∀ n, Injective (K.X n)]
    (h : (mayerVietorisPushforwardCochainShortComplex j f K).ShortExact) :
    (mayerVietorisPushforwardTriangle_eq_triangleOfSES j f K h).hom.hom₁ = 𝟙 _ :=
  rfl

/-- For an elementary distinguished square, the canonical derived module pushforward
Mayer–Vietoris triangle is distinguished. -/
theorem mayerVietorisPushforward_mem_distTriang (E : ModuleDerived X) :
    mayerVietorisPushforwardTriangle j f E ∈ distTriang (ModuleDerived X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
