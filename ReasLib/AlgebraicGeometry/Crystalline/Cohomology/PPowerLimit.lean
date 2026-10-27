/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.PPower
public import ReasLib.AlgebraicGeometry.Crystalline.Module.Sections
public import ReasLib.CategoryTheory.Sites.Derived.Sections.Presheaf
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Definition
public import Mathlib.CategoryTheory.Functor.OfSequence

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite CrystallineModuleSheaf

universe u

namespace AlgebraicGeometry.Scheme.Crystalline.PPower

noncomputable section

variable (p : ℕ) [Fact (Nat.Prime p)] {A : Type u} [CommRing A]
  [Algebra (Int.LocalizationAtPrime p) A]
variable (I : (Spec (.of A)).IdealSheafData)
  (γ : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (I.ideal V))
  (h_compatible : ∀ (V : (Spec (.of A)).affineOpens) (f : Γ(Spec (.of A), V)),
    (γ V).IsDPMorphism (γ ((Spec (.of A)).affineBasicOpen f))
      ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le f)).op).hom)
  (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
  (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))

/-- Restriction of an abelian crystalline sheaf to the full prime-power subsite. -/
def restrict
    (M : Sheaf (smallCrystallineTopology p (Spec (.of A)) I γ h_compatible
      (baseMap A p) X x₀ h_p) AddCommGrpCat.{u + 1}) (e : ℕ) :
    Sheaf (stageTopology p I γ h_compatible X x₀ h_p e) AddCommGrpCat.{u + 1} :=
  ((ObjectProperty.ι (fun T : smallCrystallineSite (Spec (.of A)) I γ h_compatible X x₀ ↦
      FactorsThrough p e T.obj.1)).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (stageTopology p I γ h_compatible X x₀ h_p e)
    (smallCrystallineTopology p (Spec (.of A)) I γ h_compatible (baseMap A p) X x₀ h_p)).obj M

/-- The underlying presheaf of stage restriction is precomposition with the inclusion. -/
theorem restrict_obj
    (M : Sheaf (smallCrystallineTopology p (Spec (.of A)) I γ h_compatible
      (baseMap A p) X x₀ h_p) AddCommGrpCat.{u + 1}) (e : ℕ) :
    (restrict p I γ h_compatible X x₀ h_p M e).obj =
      (ObjectProperty.ι (fun T : smallCrystallineSite (Spec (.of A)) I γ h_compatible X x₀ ↦
        FactorsThrough p e T.obj.1)).op ⋙ M.obj := sorry

/-- Derived sections of an abelian crystalline sheaf over a prime-power-stage presheaf. -/
def rGammaStage
    (M : Sheaf (smallCrystallineTopology p (Spec (.of A)) I γ h_compatible
      (baseMap A p) X x₀ h_p) AddCommGrpCat.{u + 1}) (e : ℕ) :
    DerivedCategory AddCommGrpCat.{u + 1} :=
  (GrothendieckTopology.Derived.Sections.Presheaf.derived
    (smallCrystallineTopology p (Spec (.of A)) I γ h_compatible (baseMap A p) X x₀ h_p)
    (stagePresheaf p I γ h_compatible X x₀ e)).obj
      ((DerivedCategory.singleFunctor _ 0).obj M)

/-- The canonical derived restriction from the successor stage to the preceding stage. -/
def rGammaStep
    (M : Sheaf (smallCrystallineTopology p (Spec (.of A)) I γ h_compatible
      (baseMap A p) X x₀ h_p) AddCommGrpCat.{u + 1}) (e : ℕ) :
    rGammaStage p I γ h_compatible X x₀ h_p M (e + 1) ⟶
      rGammaStage p I γ h_compatible X x₀ h_p M e :=
  (GrothendieckTopology.Derived.Sections.Presheaf.restriction
    (smallCrystallineTopology p (Spec (.of A)) I γ h_compatible (baseMap A p) X x₀ h_p)
    (stageInclusion p I γ h_compatible X x₀ (Nat.le_succ e))).app
      ((DerivedCategory.singleFunctor _ 0).obj M)

/-- The inverse tower of derived sections over prime-power stages beyond a cutoff. -/
def rGammaSystem
    (M : Sheaf (smallCrystallineTopology p (Spec (.of A)) I γ h_compatible
      (baseMap A p) X x₀ h_p) AddCommGrpCat.{u + 1}) (e₀ : ℕ) :
    SequentialInverseSystem (DerivedCategory AddCommGrpCat.{u + 1}) :=
  Functor.ofOpSequence (X := fun n ↦ rGammaStage p I γ h_compatible X x₀ h_p M (e₀ + n))
    (fun n ↦ rGammaStep p I γ h_compatible X x₀ h_p M (e₀ + n))

/-- Evaluation of the derived-section tower gives the corresponding prime-power stage. -/
theorem rGammaSystem_obj
    (M : Sheaf (smallCrystallineTopology p (Spec (.of A)) I γ h_compatible
      (baseMap A p) X x₀ h_p) AddCommGrpCat.{u + 1}) (e₀ n : ℕ) :
    (rGammaSystem p I γ h_compatible X x₀ h_p M e₀).obj (op n) =
      rGammaStage p I γ h_compatible X x₀ h_p M (e₀ + n) := sorry

/-- Presheaf-derived stage sections agree with derived global sections on the full subsite. -/
theorem rGammaStage_iso
    (M : Sheaf (smallCrystallineTopology p (Spec (.of A)) I γ h_compatible
      (baseMap A p) X x₀ h_p) AddCommGrpCat.{u + 1}) (e : ℕ) :
    IsIsomorphic (rGammaStage p I γ h_compatible X x₀ h_p M e)
      ((siteAbelianGlobalSectionsDerived (stageTopology p I γ h_compatible X x₀ h_p e)).obj
        ((DerivedCategory.singleFunctor
          (Sheaf (stageTopology p I γ h_compatible X x₀ h_p e) AddCommGrpCat.{u + 1}) 0).obj
            (restrict p I γ h_compatible X x₀ h_p M e))) := sorry

/-- Over an affine prime-local divided-power base, crystalline cohomology of any module
sheaf is the homotopy limit of its derived sections on a stable prime-power tail. -/
theorem cohomologyRlim (h_I_quasiCoherent : I.toModule.IsQuasicoherent)
    (h_pAmodI : IsNilpotent (Ideal.Quotient.mk
      (I.ideal ⟨⊤, isAffineOpen_top (Spec (.of A))⟩) (p : Γ(Spec (.of A), ⊤))))
    (F : CrisModuleSheaf (Spec (.of A)) I γ h_compatible X x₀)
    (hF : CrystallineModuleSheaf.IsCrisSheaf p (baseMap A p) h_p F)
    (e₀ : ℕ) (h_tail : StableTail p I γ e₀) :
    HomotopyLimit.IsOf
      (rGammaSystem p I γ h_compatible X x₀ h_p (hF.abelianSheafULift p (baseMap A p) h_p) e₀)
      ((siteAbelianGlobalSectionsDerived
        (smallCrystallineTopology p (Spec (.of A)) I γ h_compatible (baseMap A p) X x₀ h_p)).obj
          ((DerivedCategory.singleFunctor
            (Sheaf (smallCrystallineTopology p (Spec (.of A)) I γ h_compatible
              (baseMap A p) X x₀ h_p) AddCommGrpCat.{u + 1}) 0).obj
                (hF.abelianSheafULift p (baseMap A p) h_p))) := sorry

end

end AlgebraicGeometry.Scheme.Crystalline.PPower
