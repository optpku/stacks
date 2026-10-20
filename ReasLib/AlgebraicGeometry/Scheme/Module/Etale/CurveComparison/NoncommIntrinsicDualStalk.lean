/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommFiniteCoefficient
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.RootsStalkEvaluation

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.GeometricPoint
noncomputable section
universe u

namespace NoncommIntrinsicDualStalk
variable {K : Type u} [Field K] [hclosed : IsAlgClosed K]
variable (X : SchemeOverField K) [ConnectedSpace X.left] (xbar : GeometricPoint X.left)
variable (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
variable [X.left.smallEtaleTopology.HasSheafCompose (NoncommFiniteCoefficient.modules Λ)]
variable [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : X.left.Etale, HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [HasWeakSheafify X.left.smallEtaleTopology
    (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card Λ)))]
variable [∀ U : X.left.Etale, HasWeakSheafify (X.left.smallEtaleTopology.over U)
    (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card Λ)))]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u + 1}]

/-- The ground-field embedding is read from the geometric point's actual
structure morphism, using the affine global-sections counits. -/
def fieldMap : K →+* xbar.K :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
    Scheme.Γ.map (xbar.hom ≫ X.hom).op ≫
    (Scheme.ΓSpecIso (CommRingCat.of xbar.K)).hom).hom

/-- Actual extension of roots along the field embedding. -/
def rootsMap (n : ℕ) : Additive (rootsOfUnity n K) →+ Additive (rootsOfUnity n xbar.K) where
  toFun z := Additive.ofMul ⟨Units.map (fieldMap X xbar).toMonoidHom z.toMul.val, by sorry⟩
  map_zero' := sorry
  map_add' := sorry

include hclosed in
/-- Over an algebraically closed ground field all roots already belong to K. -/
theorem rootsMap_bijective (n : ℕ) (hpos : 0 < n) : Function.Bijective (rootsMap X xbar n) := sorry

def rootsEquiv (n : ℕ) (hpos : 0 < n) : Additive (rootsOfUnity n K) ≃+ Additive (rootsOfUnity n xbar.K) :=
  AddEquiv.ofBijective (rootsMap X xbar n) (rootsMap_bijective X xbar n hpos)

instance modules_preservesPointColimits :
    PreservesFilteredColimitsOfSize.{u, u} (NoncommFiniteCoefficient.modules Λ :
      ModuleCat.{u + 1} Λ ⥤ ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card Λ))) := sorry

/-- Restriction of scalars commutes with the actual filtered stalk colimit. -/
def scalarStalkIso (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (StalkRepresentation.stalk (ActualRootsModule.Coeff.{u} (Nat.card Λ)) xbar).obj
      ((NoncommFiniteCoefficient.sheaves Λ X.left).obj F) ≅
    (NoncommFiniteCoefficient.modules Λ).obj ((StalkRepresentation.stalk Λ xbar).obj F) :=
  ((AlgebraicGeometry.Scheme.GeometricPoint.toSmallEtalePoint xbar).presheafFiberCompIso (NoncommFiniteCoefficient.modules Λ :
    ModuleCat.{u + 1} Λ ⥤ ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card Λ)))).app F.obj

/-- Evaluate an intrinsic dual germ on a source germ, then evaluate its roots
germ and descend the value along the specified ground-field embedding. -/
def map (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (StalkRepresentation.stalk (ActualRootsModule.Coeff.{u} (Nat.card Λ)) xbar).obj
      (NoncommFiniteCoefficient.dual Λ X.left F) →+
    ((StalkRepresentation.stalk Λ xbar).obj F →+ Additive (rootsOfUnity (Nat.card Λ) K)) where
  toFun α :=
    { toFun s := (rootsEquiv X xbar (Nat.card Λ)
        (NoncommFiniteCoefficient.card_pos Λ)).symm
        (ActualRootsStalk.map xbar (Nat.card Λ)
          ((ActualLinearHomStalk.map (ActualRootsModule.Coeff.{u} (Nat.card Λ)) xbar
            ((NoncommFiniteCoefficient.sheaves Λ X.left).obj F)
            (ActualRootsModule.liftedSheaf X.left (Nat.card Λ)) α)
              ((scalarStalkIso X xbar Λ F).inv s)))
      map_zero' := sorry
      map_add' := sorry }
  map_zero' := sorry
  map_add' := sorry

variable (hΛ : IsUnit (Nat.card Λ : K))
variable (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ))
variable [hF : Sheaf.IsFiniteTypeLocallyConstantModule F]

include hΛ hF in
/-- Finite coefficients, local constancy and invertible order make this exact
germ-evaluation map bijective. Z/n linearity is the same as additivity here. -/
theorem map_bijective : Function.Bijective (map X xbar Λ F) := sorry

def equiv :
    (StalkRepresentation.stalk (ActualRootsModule.Coeff.{u} (Nat.card Λ)) xbar).obj
      (NoncommFiniteCoefficient.dual Λ X.left F) ≃+
    ((StalkRepresentation.stalk Λ xbar).obj F →+ Additive (rootsOfUnity (Nat.card Λ) K)) :=
  AddEquiv.ofBijective (map X xbar Λ F) (map_bijective X xbar Λ hΛ F)

end NoncommIntrinsicDualStalk
