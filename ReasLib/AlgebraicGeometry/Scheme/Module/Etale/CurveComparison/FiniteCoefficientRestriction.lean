/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.DualSheafTracePairing
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.GeometricCyclotomic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.RingTheory.Finiteness.Cardinality

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u v

namespace ActualFiniteCoefficient
variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The scalar map is the existing cardinality quotient composed with ULift.down. -/
def scalarHom : ActualRootsModule.Coeff.{u} (Nat.card Λ) →+* Λ :=
  (AlgebraicGeometry.Scheme.Etale.zmodCardRingHom (Λ := Λ)).comp ULift.ringEquiv.toRingHom

abbrev modules := ModuleCat.restrictScalars (scalarHom Λ)

variable (Y : Scheme.{u})
variable [Y.smallEtaleTopology.HasSheafCompose (modules Λ)]

/-- Restrict coefficients on the same sections and restriction maps. -/
abbrev sheaves := sheafCompose Y.smallEtaleTopology (modules Λ)

instance sheaves_additive : (sheaves Λ Y).Additive where
  map_add := by
    intros F G f g
    ext U m
    rfl
instance sheaves_preservesFiniteLimits : PreservesFiniteLimits
    (sheaves Λ Y : Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{v} (ActualRootsModule.Coeff.{u} (Nat.card Λ)))) where
  preservesFiniteLimits J _ _ := by
    letI : HasLimitsOfShape J (ModuleCat.{v} Λ) := ModuleCat.hasLimitsOfShape
    letI : HasLimitsOfShape J
        (ModuleCat.{v} (ActualRootsModule.Coeff.{u} (Nat.card Λ))) := ModuleCat.hasLimitsOfShape
    letI : PreservesLimitsOfShape J (ModuleCat.restrictScalars.{v} (scalarHom Λ)) :=
      { preservesLimit := fun {K} ↦ ModuleCat.preservesLimit_restrictScalars (scalarHom Λ) K }
    letI : PreservesLimitsOfShape J
        (sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) :=
      preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimitsOfShape _
    letI : PreservesLimitsOfShape J
        ((Functor.whiskeringRight Y.Etaleᵒᵖ _ _).obj
          (ModuleCat.restrictScalars.{v} (scalarHom Λ))) :=
      whiskeringRight_preservesLimitsOfShape _
    letI : PreservesLimitsOfShape J (sheaves Λ Y ⋙ sheafToPresheaf _ _) :=
      comp_preservesLimitsOfShape
        (sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))
        ((Functor.whiskeringRight Y.Etaleᵒᵖ _ _).obj
          (ModuleCat.restrictScalars.{v} (scalarHom Λ)))
    exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf _ _)
instance sheaves_preservesFiniteColimits : PreservesFiniteColimits (sheaves Λ Y) := sorry

variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [HasWeakSheafify Y.smallEtaleTopology
    (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card Λ)))]
variable [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U)
    (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card Λ)))]

/-- Finite locally constant Lambda modules remain finite locally constant over
Z/(card Lambda); this uses finiteness of the coefficient ring. -/
instance sheaves_finiteLocallyConstant [Finite Λ]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Sheaf.IsFiniteTypeLocallyConstantModule F] :
    Sheaf.IsFiniteTypeLocallyConstantModule ((sheaves Λ Y).obj F) := by
  let T : ModuleCat.{u + 1} Λ ⥤
      ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card Λ)) := modules Λ
  letI : PreservesLimitsOfSize.{u + 1, u + 1} T :=
    { preservesLimitsOfShape := fun {J} _ ↦
        { preservesLimit := fun {K} ↦ ModuleCat.preservesLimit_restrictScalars (scalarHom Λ) K } }
  letI : T.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} (scalarHom Λ)).isLeftAdjoint
  constructor
  intro U
  obtain ⟨I, X, hX, hF⟩ := Sheaf.IsLocallyConstantWith.existsConstantCover
    (P := fun M : ModuleCat.{u + 1} Λ ↦ Module.Finite Λ M) (F := F) U
  refine ⟨I, X, hX, ?_⟩
  intro i
  obtain ⟨M, hM, ⟨e⟩⟩ := hF i
  letI : Module.Finite Λ M := hM
  letI : Finite M := Module.finite_of_finite Λ
  letI : Finite (T.obj M) := inferInstanceAs (Finite M)
  refine ⟨T.obj M, Module.Finite.of_finite, ⟨?_⟩⟩
  exact (sheafCompose (Y.smallEtaleTopology.over (X i).left) T).mapIso e ≪≫
    (constantCommuteCompose (Y.smallEtaleTopology.over (X i).left) T).app M

variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]

/-- The intrinsic additive dual sheaf used by the normalized geometric trace. -/
def dual (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  ActualLinearSheafHom.obj Y (ActualRootsModule.Coeff.{u} (Nat.card Λ))
    ((sheaves Λ Y).obj F) (ActualRootsModule.liftedSheaf Y (Nat.card Λ))

/-- Scalar multiplication on a Lambda sheaf is an actual sheaf endomorphism. -/
def scalarEnd (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (a : Λ) : F ⟶ F :=
  ObjectProperty.homMk
    { app := fun U ↦ ModuleCat.ofHom (a • LinearMap.id)
      naturality := by
        intro U V f
        ext m
        exact ((F.obj.map f).hom.map_smul a m).symm }

/-- Lambda acts on the intrinsic dual by precomposition on the source, not
by an invented Lambda action on roots of unity. -/
def dualScalarEnd (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (a : Λ) :
    dual Λ Y F ⟶ dual Λ Y F :=
  ObjectProperty.homMk
    { app := fun U ↦ ModuleCat.ofHom
        { toFun := fun φ ↦ Functor.whiskerLeft (Over.forget U.unop).op
            ((sheaves Λ Y).map (scalarEnd Λ Y F a)).hom ≫ φ
          map_add' := by
            intro φ ψ
            ext V m
            rfl
          map_smul' := by
            intro c φ
            ext V m
            rfl }
      naturality := by
        intro U V f
        ext φ
        rfl }

/-- Restricting scalars forgets no additive coefficient data. -/
def underlyingIso
    [Y.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})]
    [Y.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card Λ))) AddCommGrpCat.{u + 1})]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (ActualSiteExt.moduleForget Y (ActualRootsModule.Coeff.{u} (Nat.card Λ))).obj
      ((sheaves Λ Y).obj F) ≅ (ActualSiteExt.moduleForget Y Λ).obj F :=
  Iso.refl _

end ActualFiniteCoefficient
