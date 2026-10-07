module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.DualSheafTracePairing
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.GeometricCyclotomic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace ActualFiniteCoefficient
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The scalar map is the existing cardinality quotient composed with ULift.down. -/
def scalarHom : ActualRootsModule.Coeff.{u} (Nat.card Λ) →+* Λ :=
  (AlgebraicGeometry.Scheme.Etale.zmodCardRingHom (Λ := Λ)).comp ULift.ringEquiv.toRingHom

abbrev modules := ModuleCat.restrictScalars (scalarHom Λ)

variable (Y : Scheme.{u})
variable [Y.smallEtaleTopology.HasSheafCompose (modules Λ)]

/-- Restrict coefficients on the same sections and restriction maps. -/
abbrev sheaves := sheafCompose Y.smallEtaleTopology (modules Λ)

instance sheaves_additive : (sheaves Λ Y).Additive := sorry
instance sheaves_preservesFiniteLimits : PreservesFiniteLimits (sheaves Λ Y) := sorry
instance sheaves_preservesFiniteColimits : PreservesFiniteColimits (sheaves Λ Y) := sorry

variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [HasWeakSheafify Y.smallEtaleTopology
    (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card Λ)))]
variable [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U)
    (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card Λ)))]

/-- Finite locally constant Lambda modules remain finite locally constant over
Z/(card Lambda); this uses finiteness of the coefficient ring. -/
instance sheaves_finiteLocallyConstant
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Sheaf.IsFiniteTypeLocallyConstantModule F] :
    Sheaf.IsFiniteTypeLocallyConstantModule ((sheaves Λ Y).obj F) := sorry

variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]

/-- The intrinsic additive dual sheaf used by the normalized geometric trace. -/
def dual (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  ActualLinearSheafHom.obj Y (ActualRootsModule.Coeff.{u} (Nat.card Λ))
    ((sheaves Λ Y).obj F) (ActualRootsModule.liftedSheaf Y (Nat.card Λ))

/-- Scalar multiplication on a Lambda sheaf is an actual sheaf endomorphism. -/
def scalarEnd (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (a : Λ) : F ⟶ F :=
  ObjectProperty.homMk
    { app := fun U ↦ ModuleCat.ofHom (a • LinearMap.id)
      naturality := sorry }

/-- Lambda acts on the intrinsic dual by precomposition on the source, not
by an invented Lambda action on roots of unity. -/
def dualScalarEnd (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (a : Λ) :
    dual Λ Y F ⟶ dual Λ Y F :=
  ObjectProperty.homMk
    { app := fun U ↦ ModuleCat.ofHom
        { toFun := fun φ ↦ Functor.whiskerLeft (Over.forget U.unop).op
            ((sheaves Λ Y).map (scalarEnd Λ Y F a)).hom ≫ φ
          map_add' := sorry
          map_smul' := sorry }
      naturality := sorry }

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
