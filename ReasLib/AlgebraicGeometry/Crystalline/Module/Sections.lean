/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.ULift
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import ReasLib.AlgebraicGeometry.Crystalline.Module

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Crystalline
open AlgebraicGeometry.Scheme.Modules
open CrystallineModuleSheaf

@[expose] public section

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme.Crystalline

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (S : Scheme.{u}) (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))

/-- Global sections of a module sheaf, viewed as an abelian group. -/
def abelianGlobalSections {Y : Scheme.{u}} (M : Y.Modules) : AddCommGrpCat.{u} :=
  (Scheme.Modules.presheaf M).obj (op ⊤)

/-- Unfolding of abelian global sections as top-open values of the underlying presheaf. -/
theorem abelianGlobalSections_eq {Y : Scheme.{u}} (M : Y.Modules) :
    abelianGlobalSections M = (Scheme.Modules.presheaf M).obj (op ⊤) :=
  rfl

/-- Global sections along a thickening morphism, after applying a module comparison. -/
def abelianGlobalSections_map {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    {MY : Y.Modules} {MZ : Z.Modules}
    (φ : (Scheme.Modules.pullback f).obj MZ ⟶ MY) :
    abelianGlobalSections MZ ⟶ abelianGlobalSections MY :=
  Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app MZ) ⊤ ≫
    eqToHom
      (by
        have hU : f ⁻¹ᵁ (⊤ : Z.Opens) = ⊤ := rfl
        change
          (Scheme.Modules.presheaf
              ((Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj MZ))).obj
            (op ⊤) =
          (Scheme.Modules.presheaf ((Scheme.Modules.pullback f).obj MZ)).obj (op ⊤)
        simp [Scheme.Modules.pushforward_obj_obj, hU]) ≫
    Modules.Hom.app φ ⊤

/-- Global sections of the canonical identity Scheme.Modules.pullback comparison give the identity map. -/
theorem abelianGlobalSections_map_id {Y : Scheme.{u}} (M : Y.Modules) :
    abelianGlobalSections_map (𝟙 Y) ((pullbackId Y).hom.app M) =
      𝟙 (abelianGlobalSections M) := sorry

/-- Global section maps compose contravariantly through the canonical Scheme.Modules.pullback compositor. -/
theorem abelianGlobalSections_map_comp {Y Z W : Scheme.{u}}
    (f : Y ⟶ Z) (g : Z ⟶ W) {MY : Y.Modules} {MZ : Z.Modules} {MW : W.Modules}
    (cf : (Scheme.Modules.pullback f).obj MZ ⟶ MY) (cg : (Scheme.Modules.pullback g).obj MW ⟶ MZ) :
    abelianGlobalSections_map (f ≫ g)
        ((pullbackComp f g).inv.app MW ≫ (Scheme.Modules.pullback f).map cg ≫ cf) =
      abelianGlobalSections_map g cg ≫ abelianGlobalSections_map f cf := sorry

/-- The abelian presheaf of global sections of a crystalline module sheaf on `Cris(X/S)`. -/
def toAbelianPresheaf (F : CrisModuleSheaf S I γ h_compatible X x₀) :
    (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj T := abelianGlobalSections (F.obj T.unop)
  map {T U} f :=
    abelianGlobalSections_map
      (smallCrystallineHom_thickening S I γ h_compatible X x₀ f.unop)
      (F.comparison f.unop)
  map_id T := by
    have h := F.comparison_id T.unop
    change F.comparison (𝟙 T.unop) = 𝟙 _ ≫ _ at h
    rw [Category.id_comp] at h
    change abelianGlobalSections_map (𝟙 _) (F.comparison (𝟙 T.unop)) = _
    rw [h]
    exact abelianGlobalSections_map_id (F.obj T.unop)
  map_comp f g := by
    have h := F.comparison_comp g.unop f.unop
    change F.comparison (g.unop ≫ f.unop) = 𝟙 _ ≫ _ ≫ _ ≫ _ at h
    rw [Category.id_comp] at h
    change abelianGlobalSections_map (g.unop.hom.thickening ≫ f.unop.hom.thickening)
      (F.comparison (g.unop ≫ f.unop)) = _
    rw [h]
    exact abelianGlobalSections_map_comp g.unop.hom.thickening f.unop.hom.thickening
      (F.comparison g.unop) (F.comparison f.unop)

/-- Underlying abelian sheaf of a crystalline module sheaf on the small crystalline site. -/
def toAbelianSheaf
    [HasWeakSheafify (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      AddCommGrpCat.{u}]
    (F : CrisModuleSheaf S I γ h_compatible X x₀) :
    Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u} :=
  (presheafToSheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      AddCommGrpCat.{u}).obj
    (toAbelianPresheaf S I γ h_compatible X x₀ F)

/-- Sheafification of the global-section presheaf recovers `toAbelianSheaf`. -/
theorem toAbelianSheaf_obj
    [HasWeakSheafify (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      AddCommGrpCat.{u}]
    (F : CrisModuleSheaf S I γ h_compatible X x₀) :
    toAbelianSheaf p S I γ h_compatible s X x₀ h_p F =
      (presheafToSheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
          AddCommGrpCat.{u}).obj
        (toAbelianPresheaf S I γ h_compatible X x₀ F) :=
  rfl

/-- Restriction of an abelian sheaf on `Cris(X/S)` to the chaotic whole-source subcategory. -/
def restrictToChaotic
    (F : Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{w}) :
    Sheaf (chaoticTopology S I γ h_compatible X x₀) AddCommGrpCat.{w} where
  obj := (chaoticInclusion S I γ h_compatible X x₀).op ⋙ F.obj
  property := Presheaf.isSheaf_bot _

/-- Restriction to the chaotic site is composition with the opposite inclusion. -/
theorem restrictToChaotic_obj
    (F : Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{w}) :
    (restrictToChaotic p S I γ h_compatible s X x₀ h_p F).obj =
      (chaoticInclusion S I γ h_compatible X x₀).op ⋙ F.obj :=
  rfl

end AlgebraicGeometry.Scheme.Crystalline

namespace CrystallineModuleSheaf

variable {S : Scheme.{u}} {I : S.IdealSheafData}
variable {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
variable {h_compatible : ∀ (V : S.affineOpens) (f : Γ(S, V)),
  (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
    (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
variable {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}

/-- The intrinsic coherence and Zariski descent laws for a crystalline module assignment.
The open-immersion condition identifies its module sheaves with restrictions of one sheaf;
comparisons along general morphisms need not be isomorphisms. -/
structure IsCrisSheaf.{v}
    {S : Scheme.{v}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{v}} {x₀ : X ⟶ I.subscheme}
    (p : ℕ) [Fact (Nat.Prime p)]
    (s : S ⟶ Spec (.of (ULift.{v} (Int.LocalizationAtPrime p))))
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (F : CrisModuleSheaf S I γ h_compatible X x₀) : Prop where
  /-- Comparisons preserve identity morphisms, using canonical Scheme.Modules.pullback identification. -/
  comparison_id (T : smallCrystallineSite S I γ h_compatible X x₀) :
    F.comparison (𝟙 T) = (pullbackId T.obj.1.thickening).hom.app (F.obj T)
  /-- Comparisons preserve composition, using the canonical Scheme.Modules.pullback compositor. -/
  comparison_comp {T U V : smallCrystallineSite S I γ h_compatible X x₀}
      (f : T ⟶ U) (g : U ⟶ V) :
    F.comparison (f ≫ g) =
      (pullbackComp f.hom.thickening g.hom.thickening).inv.app (F.obj V) ≫
        (Scheme.Modules.pullback f.hom.thickening).map (F.comparison g) ≫ F.comparison f
  /-- Restricting a thickening to an open restricts its assigned module sheaf. -/
  restriction {T U : smallCrystallineSite S I γ h_compatible X x₀} (f : T ⟶ U)
      (h_open : IsOpenImmersion f.hom.thickening) : IsIso (F.comparison f)
  /-- Global sections of the assignments satisfy descent on the crystalline site. -/
  descent : Presheaf.IsSheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
    (toAbelianPresheaf S I γ h_compatible X x₀ F)

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))

/-- Recognize a genuine crystalline sheaf from its intrinsic comparison and descent laws. -/
def IsCrisSheaf.of (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (comparison_id : ∀ T : smallCrystallineSite S I γ h_compatible X x₀,
      F.comparison (𝟙 T) = (pullbackId T.obj.1.thickening).hom.app (F.obj T))
    (comparison_comp : ∀ {T U V : smallCrystallineSite S I γ h_compatible X x₀}
      (f : T ⟶ U) (g : U ⟶ V),
      F.comparison (f ≫ g) =
        (pullbackComp f.hom.thickening g.hom.thickening).inv.app (F.obj V) ≫
          (Scheme.Modules.pullback f.hom.thickening).map (F.comparison g) ≫ F.comparison f)
    (restriction : ∀ {T U : smallCrystallineSite S I γ h_compatible X x₀}
      (f : T ⟶ U), IsOpenImmersion f.hom.thickening → IsIso (F.comparison f))
    (descent : Presheaf.IsSheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (toAbelianPresheaf S I γ h_compatible X x₀ F)) : IsCrisSheaf p s h_p F :=
  { comparison_id, comparison_comp, restriction, descent }

/-- A genuine crystalline sheaf has both identity and composition compatibility. -/
theorem IsCrisSheaf.comparison_spec {F : CrisModuleSheaf S I γ h_compatible X x₀}
    (hF : IsCrisSheaf p s h_p F) :
    (∀ T : smallCrystallineSite S I γ h_compatible X x₀,
      F.comparison (𝟙 T) = (pullbackId T.obj.1.thickening).hom.app (F.obj T)) ∧
    (∀ {T U V : smallCrystallineSite S I γ h_compatible X x₀} (f : T ⟶ U) (g : U ⟶ V),
      F.comparison (f ≫ g) =
        (pullbackComp f.hom.thickening g.hom.thickening).inv.app (F.obj V) ≫
          (Scheme.Modules.pullback f.hom.thickening).map (F.comparison g) ≫ F.comparison f) := ⟨hF.comparison_id, hF.comparison_comp⟩

/-- A genuine crystalline sheaf restricts correctly to opens and satisfies descent. -/
theorem IsCrisSheaf.descent_spec {F : CrisModuleSheaf S I γ h_compatible X x₀}
    (hF : IsCrisSheaf p s h_p F) :
    (∀ {T U : smallCrystallineSite S I γ h_compatible X x₀} (f : T ⟶ U),
      IsOpenImmersion f.hom.thickening → IsIso (F.comparison f)) ∧
    Presheaf.IsSheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (toAbelianPresheaf S I γ h_compatible X x₀ F) := ⟨hF.restriction, hF.descent⟩

/-- The underlying abelian sheaf of a coherent crystalline module assignment, with its
actual sections and comparison maps, rather than an unrelated sheafification. -/
def IsCrisSheaf.abelianSheaf {F : CrisModuleSheaf S I γ h_compatible X x₀}
    (hF : IsCrisSheaf p s h_p F) :
    Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u} :=
  ⟨toAbelianPresheaf S I γ h_compatible X x₀ F, hF.descent⟩

/-- The abelian sheaf has exactly the sections and restriction maps induced by the assignment. -/
theorem IsCrisSheaf.abelianSheaf_obj {F : CrisModuleSheaf S I γ h_compatible X x₀}
    (hF : IsCrisSheaf p s h_p F) :
    (hF.abelianSheaf p s h_p).obj = toAbelianPresheaf S I γ h_compatible X x₀ F := rfl

/-- The canonical universe lift of the underlying abelian sheaf of a crystalline module. -/
def IsCrisSheaf.abelianSheafULift {F : CrisModuleSheaf S I γ h_compatible X x₀}
    (hF : IsCrisSheaf p s h_p F) :
    Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u + 1} :=
  (sheafCompose (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
    AddCommGrpCat.uliftFunctor.{u + 1, u}).obj (hF.abelianSheaf p s h_p)

/-- The underlying presheaf of the lifted abelian sheaf is the canonical universe lift of
the crystalline section presheaf. -/
theorem IsCrisSheaf.abelianSheafULift_obj {F : CrisModuleSheaf S I γ h_compatible X x₀}
    (hF : IsCrisSheaf p s h_p F) :
    (hF.abelianSheafULift p s h_p).obj =
      toAbelianPresheaf S I γ h_compatible X x₀ F ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u} := sorry

end CrystallineModuleSheaf

namespace AlgebraicGeometry.Scheme.Crystalline

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (S : Scheme.{u}) (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))


/-- For affine `X` and `S`, for every locally
quasi-coherent `𝒪_{X/S}`-module `F` the derived global sections on the chaotic full
subcategory of whole-source objects `(X, T, δ)` recover the derived global sections on
`Cris(X/S)`. -/
theorem locallyQuasiCoherent_derivedGlobalSections_iso_chaotic
    [IsAffine X] [IsAffine S]
    (h_I_quasiCoherent : I.toModule.IsQuasicoherent)
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    [ModuleSheaf.IsLocallyQuasiCoherent F]
    (hF : IsCrisSheaf p s h_p F) :
    IsIsomorphic
      ((siteAbelianGlobalSectionsDerived (chaoticTopology S I γ h_compatible X x₀)).obj
        ((DerivedCategory.singleFunctor
            (Sheaf (chaoticTopology S I γ h_compatible X x₀) AddCommGrpCat.{u + 1}) 0).obj
          (restrictToChaotic p S I γ h_compatible s X x₀ h_p
            (hF.abelianSheafULift p s h_p))))
      ((siteAbelianGlobalSectionsDerived
          (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)).obj
        ((DerivedCategory.singleFunctor
            (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
              AddCommGrpCat.{u + 1}) 0).obj
          (hF.abelianSheafULift p s h_p))) := sorry

end AlgebraicGeometry.Scheme.Crystalline
