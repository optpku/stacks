/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite

/-!
# Trivial square-zero extension sheaves on a ringed site

The sheaf of algebras `R ⊕ N` on a site, with objectwise `TrivSqZeroExt` rings.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.TrivSqZeroExt

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The canonical right action of a commutative ring on one of its modules. -/
instance instModuleMulOpposite (R : CommRingCat.{w}) (M : ModuleCat.{w} R) :
    Module Rᵐᵒᵖ M :=
  Module.compHom M ((RingHom.id R).fromOpposite fun x y ↦ mul_comm x y)

/-- The canonical left and right actions of a commutative ring on a module agree. -/
theorem opposite_smul_eq_smul (R : CommRingCat.{w}) (M : ModuleCat.{w} R) (r : R) (x : M) :
    MulOpposite.op r • x = r • x := sorry

/-- The canonical left and right actions of a commutative ring on a module agree. -/
instance instIsCentralScalar (R : CommRingCat.{w}) (M : ModuleCat.{w} R) :
    IsCentralScalar R M where
  op_smul_eq_smul := opposite_smul_eq_smul R M

/-- The trivial square-zero extension of the sections of `R` by the sections of `N` over `U`. -/
def sectionRing (R : Sheaf J CommRingCat.{w}) (N : SheafOfModules.{w} (ringSheaf J R))
    (U : Cᵒᵖ) : CommRingCat.{w} :=
  CommRingCat.of (_root_.TrivSqZeroExt (R.obj.obj U) (N.val.obj U))

/-- Restriction of a section of `R ⊕ N` along a morphism of the site. -/
def restrictionApply (R : Sheaf J CommRingCat.{w}) (N : SheafOfModules.{w} (ringSheaf J R))
    {U V : Cᵒᵖ} (rho : U ⟶ V) (x : sectionRing R N U) : sectionRing R N V :=
  (R.obj.map rho x.1, N.val.map rho x.2)

/-- Restriction of `R ⊕ N` preserves zero. -/
theorem restrictionApply_zero (R : Sheaf J CommRingCat.{w})
    (N : SheafOfModules.{w} (ringSheaf J R)) {U V : Cᵒᵖ} (rho : U ⟶ V) :
    restrictionApply R N rho 0 = 0 := sorry

/-- Restriction of `R ⊕ N` preserves one. -/
theorem restrictionApply_one (R : Sheaf J CommRingCat.{w})
    (N : SheafOfModules.{w} (ringSheaf J R)) {U V : Cᵒᵖ} (rho : U ⟶ V) :
    restrictionApply R N rho 1 = 1 := sorry

/-- Restriction of `R ⊕ N` preserves addition. -/
theorem restrictionApply_add (R : Sheaf J CommRingCat.{w})
    (N : SheafOfModules.{w} (ringSheaf J R)) {U V : Cᵒᵖ} (rho : U ⟶ V)
    (x y : sectionRing R N U) :
    restrictionApply R N rho (x + y) =
      restrictionApply R N rho x + restrictionApply R N rho y := sorry

/-- Restriction of `R ⊕ N` preserves multiplication. -/
theorem restrictionApply_mul (R : Sheaf J CommRingCat.{w})
    (N : SheafOfModules.{w} (ringSheaf J R)) {U V : Cᵒᵖ} (rho : U ⟶ V)
    (x y : sectionRing R N U) :
    restrictionApply R N rho (x * y) =
      restrictionApply R N rho x * restrictionApply R N rho y := sorry

/-- Restriction maps of `R` and `N` induce restriction maps of `R ⊕ N`. -/
def restriction (R : Sheaf J CommRingCat.{w}) (N : SheafOfModules.{w} (ringSheaf J R))
    {U V : Cᵒᵖ} (rho : U ⟶ V) : sectionRing R N U ⟶ sectionRing R N V :=
  CommRingCat.ofHom
    { toFun := restrictionApply R N rho
      map_zero' := restrictionApply_zero R N rho
      map_one' := restrictionApply_one R N rho
      map_add' := restrictionApply_add R N rho
      map_mul' := restrictionApply_mul R N rho }

/-- Restriction along an identity morphism is the identity. -/
theorem restriction_id (R : Sheaf J CommRingCat.{w}) (N : SheafOfModules.{w} (ringSheaf J R))
    (U : Cᵒᵖ) : restriction R N (𝟙 U) = 𝟙 (sectionRing R N U) := sorry

/-- Restriction along a composite morphism is the composite restriction. -/
theorem restriction_comp (R : Sheaf J CommRingCat.{w}) (N : SheafOfModules.{w} (ringSheaf J R))
    {U V W : Cᵒᵖ} (rho : U ⟶ V) (sigma : V ⟶ W) :
    restriction R N (rho ≫ sigma) = restriction R N rho ≫ restriction R N sigma := sorry

/-- The presheaf of trivial square-zero extensions of a commutative ring sheaf by a module
sheaf. -/
def presheaf (R : Sheaf J CommRingCat.{w}) (N : SheafOfModules.{w} (ringSheaf J R)) :
    Cᵒᵖ ⥤ CommRingCat.{w} where
  obj U := sectionRing R N U
  map rho := restriction R N rho
  map_id U := restriction_id R N U
  map_comp rho sigma := restriction_comp R N rho sigma

/-- The presheaf of trivial square-zero extensions satisfies the sheaf condition. -/
theorem presheaf_isSheaf (R : Sheaf J CommRingCat.{w}) (N : SheafOfModules.{w} (ringSheaf J R)) :
    Presheaf.IsSheaf J (presheaf R N) := sorry

/-- The sheaf of algebras `R ⊕ N` on a ringed site. -/
def trivSqZeroExt (R : Sheaf J CommRingCat.{w}) (N : SheafOfModules.{w} (ringSheaf J R)) :
    Sheaf J CommRingCat.{w} :=
  ⟨presheaf R N, presheaf_isSheaf R N⟩

/-- The ring-sheaf projection `R ⊕ N ⟶ R` on sections. -/
def fstApply (R : Sheaf J CommRingCat.{w}) (N : SheafOfModules.{w} (ringSheaf J R))
    (U : Cᵒᵖ) (x : (trivSqZeroExt R N).obj.obj U) : R.obj.obj U :=
  _root_.TrivSqZeroExt.fst x

/-- The sectionwise projection `R ⊕ N ⟶ R` preserves zero. -/
theorem fstApply_zero (R : Sheaf J CommRingCat.{w}) (N : SheafOfModules.{w} (ringSheaf J R))
    (U : Cᵒᵖ) : fstApply R N U 0 = 0 := sorry

/-- The sectionwise projection `R ⊕ N ⟶ R` preserves one. -/
theorem fstApply_one (R : Sheaf J CommRingCat.{w}) (N : SheafOfModules.{w} (ringSheaf J R))
    (U : Cᵒᵖ) : fstApply R N U 1 = 1 := sorry

/-- The sectionwise projection `R ⊕ N ⟶ R` preserves addition. -/
theorem fstApply_add (R : Sheaf J CommRingCat.{w}) (N : SheafOfModules.{w} (ringSheaf J R))
    (U : Cᵒᵖ) (x y : (trivSqZeroExt R N).obj.obj U) :
    fstApply R N U (x + y) = fstApply R N U x + fstApply R N U y := sorry

/-- The sectionwise projection `R ⊕ N ⟶ R` preserves multiplication. -/
theorem fstApply_mul (R : Sheaf J CommRingCat.{w}) (N : SheafOfModules.{w} (ringSheaf J R))
    (U : Cᵒᵖ) (x y : (trivSqZeroExt R N).obj.obj U) :
    fstApply R N U (x * y) = fstApply R N U x * fstApply R N U y := sorry

/-- The component of the ring-sheaf projection `R ⊕ N ⟶ R` over `U`. -/
def fstApp (R : Sheaf J CommRingCat.{w}) (N : SheafOfModules.{w} (ringSheaf J R)) (U : Cᵒᵖ) :
    (trivSqZeroExt R N).obj.obj U ⟶ R.obj.obj U :=
  CommRingCat.ofHom
    { toFun := fstApply R N U
      map_zero' := fstApply_zero R N U
      map_one' := fstApply_one R N U
      map_add' := fstApply_add R N U
      map_mul' := fstApply_mul R N U }

/-- The components of `fst` commute with restriction. -/
theorem fstApp_naturality (R : Sheaf J CommRingCat.{w}) (N : SheafOfModules.{w} (ringSheaf J R))
    {U V : Cᵒᵖ} (rho : U ⟶ V) :
    (trivSqZeroExt R N).obj.map rho ≫ fstApp R N V =
      fstApp R N U ≫ R.obj.map rho := sorry

/-- The canonical projection of sheaves of algebras `R ⊕ N ⟶ R`. -/
def fst (R : Sheaf J CommRingCat.{w}) (N : SheafOfModules.{w} (ringSheaf J R)) :
    trivSqZeroExt R N ⟶ R :=
  ObjectProperty.homMk
    { app U := fstApp R N U
      naturality {U V} rho := fstApp_naturality R N rho }

/-- The algebra inclusion `R ⟶ R ⊕ N` on sections. -/
def inlApply (R : Sheaf J CommRingCat.{w}) (N : SheafOfModules.{w} (ringSheaf J R))
    (U : Cᵒᵖ) (r : R.obj.obj U) : (trivSqZeroExt R N).obj.obj U :=
  _root_.TrivSqZeroExt.inl r

/-- The sectionwise inclusion `R ⟶ R ⊕ N` preserves zero. -/
theorem inlApply_zero (R : Sheaf J CommRingCat.{w}) (N : SheafOfModules.{w} (ringSheaf J R))
    (U : Cᵒᵖ) : inlApply R N U 0 = 0 := sorry

/-- The sectionwise inclusion `R ⟶ R ⊕ N` preserves one. -/
theorem inlApply_one (R : Sheaf J CommRingCat.{w}) (N : SheafOfModules.{w} (ringSheaf J R))
    (U : Cᵒᵖ) : inlApply R N U 1 = 1 := sorry

/-- The sectionwise inclusion `R ⟶ R ⊕ N` preserves addition. -/
theorem inlApply_add (R : Sheaf J CommRingCat.{w}) (N : SheafOfModules.{w} (ringSheaf J R))
    (U : Cᵒᵖ) (r s : R.obj.obj U) :
    inlApply R N U (r + s) = inlApply R N U r + inlApply R N U s := sorry

/-- The sectionwise inclusion `R ⟶ R ⊕ N` preserves multiplication. -/
theorem inlApply_mul (R : Sheaf J CommRingCat.{w}) (N : SheafOfModules.{w} (ringSheaf J R))
    (U : Cᵒᵖ) (r s : R.obj.obj U) :
    inlApply R N U (r * s) = inlApply R N U r * inlApply R N U s := sorry

/-- The component of the algebra inclusion `R ⟶ R ⊕ N` over `U`. -/
def inlApp (R : Sheaf J CommRingCat.{w}) (N : SheafOfModules.{w} (ringSheaf J R)) (U : Cᵒᵖ) :
    R.obj.obj U ⟶ (trivSqZeroExt R N).obj.obj U :=
  CommRingCat.ofHom
    { toFun := inlApply R N U
      map_zero' := inlApply_zero R N U
      map_one' := inlApply_one R N U
      map_add' := inlApply_add R N U
      map_mul' := inlApply_mul R N U }

/-- The components of `inl` commute with restriction. -/
theorem inlApp_naturality (R : Sheaf J CommRingCat.{w}) (N : SheafOfModules.{w} (ringSheaf J R))
    {U V : Cᵒᵖ} (rho : U ⟶ V) :
    R.obj.map rho ≫ inlApp R N V =
      inlApp R N U ≫ (trivSqZeroExt R N).obj.map rho := sorry

/-- The canonical algebra structure map `R ⟶ R ⊕ N`. -/
def inl (R : Sheaf J CommRingCat.{w}) (N : SheafOfModules.{w} (ringSheaf J R)) :
    R ⟶ trivSqZeroExt R N :=
  ObjectProperty.homMk
    { app U := inlApp R N U
      naturality {U V} rho := inlApp_naturality R N rho }

/-- The algebra inclusion of `R` is a section of the projection `R ⊕ N ⟶ R`. -/
theorem fst_comp_inl (R : Sheaf J CommRingCat.{w}) (N : SheafOfModules.{w} (ringSheaf J R)) :
    inl R N ≫ fst R N = 𝟙 R := sorry

/-- The module coordinate of a section of `R ⊕ N`. -/
def snd (R : Sheaf J CommRingCat.{w}) (N : SheafOfModules.{w} (ringSheaf J R)) {U : Cᵒᵖ}
    (x : (trivSqZeroExt R N).obj.obj U) : N.val.obj U :=
  _root_.TrivSqZeroExt.snd x

/-- The additive inclusion of a module section into `R ⊕ N`. -/
def inr (R : Sheaf J CommRingCat.{w}) (N : SheafOfModules.{w} (ringSheaf J R)) {U : Cᵒᵖ}
    (m : N.val.obj U) : (trivSqZeroExt R N).obj.obj U :=
  _root_.TrivSqZeroExt.inr m

/-- The module coordinate of `R ⊕ N` is natural in the site. -/
theorem snd_naturality (R : Sheaf J CommRingCat.{w}) (N : SheafOfModules.{w} (ringSheaf J R))
    {U V : Cᵒᵖ} (rho : U ⟶ V) (x : (trivSqZeroExt R N).obj.obj U) :
    snd R N ((trivSqZeroExt R N).obj.map rho x) = N.val.map rho (snd R N x) := sorry

/-- The projection `fst` acts by the ring coordinate on sections. -/
theorem fst_apply (R : Sheaf J CommRingCat.{w}) (N : SheafOfModules.{w} (ringSheaf J R))
    (U : Cᵒᵖ) (x : (trivSqZeroExt R N).obj.obj U) :
    (fst R N).hom.app U x = fstApply R N U x := sorry

/-- The inclusion `inl` acts by the algebra inclusion on sections. -/
theorem inl_apply (R : Sheaf J CommRingCat.{w}) (N : SheafOfModules.{w} (ringSheaf J R))
    (U : Cᵒᵖ) (r : R.obj.obj U) :
    (inl R N).hom.app U r = inlApply R N U r := sorry

end SheafOfModules.RingedSite.TrivSqZeroExt
