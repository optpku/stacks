/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommResidualCoinvariantsLaws
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Residual Frobenius on continuous noncommutative homology

Derive the actual closed-coinvariant functor in compact arithmetic
representations, retaining the quotient-group action. Frobenius is that
action on the resulting complex after forgetting only the residual action.
Natural chain degree i is placed in cochain degree -i.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

-- Local instance justification (defeq pin): This module constructs the standard localized derived category used by DerivedCategory.Q throughout.
attribute [local instance] HasDerivedCategory.standard

universe u

namespace NoncommResidualHomology

variable (R G Γ Q : Type u) [Ring R] [Finite R]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
variable [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [T2Space Q]
variable (φ : G →ₜ* Γ) (ψ : Γ →ₜ* Q)
variable (hexact : MonoidHom.range φ.toMonoidHom = MonoidHom.ker ψ.toMonoidHom)
variable (hsurj : Function.Surjective ψ)

/-- Actual residual coinvariants of compact right R-modules. -/
abbrev coinvariants := NoncommResidualCoinvariants.functor Rᵐᵒᵖ G Γ Q φ ψ hexact hsurj

/-- Forget the quotient action and topology, preserving coefficient handedness. -/
def forget : NoncommCompactRepresentation.Cat Rᵐᵒᵖ Q ⥤ ModuleCat.{u} Rᵐᵒᵖ :=
  (NoncommCompactRepresentation.continuousAction Rᵐᵒᵖ Q).ι ⋙
    Action.forget (NoncommCompactModule Rᵐᵒᵖ) Q ⋙ NoncommCompactModule.forget Rᵐᵒᵖ

instance forget_additive : (forget R Q).Additive where
  map_add := by intros; rfl

/-- The actual Q-action is natural on underlying coefficient modules. -/
def residualAction (q : Q) : forget R Q ⟶ forget R Q where
  app M := (NoncommCompactModule.forget Rᵐᵒᵖ).map (M.obj.ρ q)
  naturality {M N} f := by
    change (NoncommCompactModule.forget Rᵐᵒᵖ).map f.hom.hom ≫
        (NoncommCompactModule.forget Rᵐᵒᵖ).map (N.obj.ρ q) =
      (NoncommCompactModule.forget Rᵐᵒᵖ).map (M.obj.ρ q) ≫
        (NoncommCompactModule.forget Rᵐᵒᵖ).map f.hom.hom
    simpa only [Functor.map_comp] using
      (congrArg (NoncommCompactModule.forget Rᵐᵒᵖ).map (f.hom.comm q)).symm

/-- Apply residual coinvariants to the existing continuous dual resolution. -/
def chain (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ Γ) :
    ChainComplex (NoncommCompactRepresentation.Cat Rᵐᵒᵖ Q) ℕ :=
  ((coinvariants R G Γ Q φ ψ hexact hsurj).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (NoncommDualResolution.chosen R Γ M).complex

/-- Underlying module chain; the Q-action has already been constructed before forgetting. -/
def moduleChain (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ Γ) :
    ChainComplex (ModuleCat.{u} Rᵐᵒᵖ) ℕ :=
  ((forget R Q).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (chain R G Γ Q φ ψ hexact hsurj M)

/-- Frobenius at any specified quotient-group element is a genuine chain map. -/
def chainFrobenius (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ Γ) (q : Q) :
    moduleChain R G Γ Q φ ψ hexact hsurj M ⟶
      moduleChain R G Γ Q φ ψ hexact hsurj M :=
  (NatTrans.mapHomologicalComplex (residualAction R Q q) (ComplexShape.down ℕ)).app
    (chain R G Γ Q φ ψ hexact hsurj M)

/-- Every component is the actual residual action on the closed quotient. -/
theorem chainFrobenius_f (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ Γ)
    (q : Q) (i : ℕ) :
    (chainFrobenius R G Γ Q φ ψ hexact hsurj M q).f i =
      (NoncommCompactModule.forget Rᵐᵒᵖ).map
        (((chain R G Γ Q φ ψ hexact hsurj M).X i).obj.ρ q) := rfl

/-- Termwise Frobenius sends the class of m to the class of γm for every lift γ. -/
theorem chainFrobenius_projection (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ Γ)
    (γ : Γ) (i : ℕ) (m : ((NoncommDualResolution.chosen R Γ M).complex.X i).obj.V.toModule) :
    ((chainFrobenius R G Γ Q φ ψ hexact hsurj M (ψ γ)).f i).hom
        (NoncommResidualCoinvariants.projection Rᵐᵒᵖ G Γ φ
          ((NoncommDualResolution.chosen R Γ M).complex.X i) m) =
      NoncommResidualCoinvariants.projection Rᵐᵒᵖ G Γ φ
        ((NoncommDualResolution.chosen R Γ M).complex.X i)
        ((show _ →L[Rᵐᵒᵖ] _ from
          ((NoncommDualResolution.chosen R Γ M).complex.X i).obj.ρ γ) m) :=
  NoncommResidualCoinvariants.action_projection_lift Rᵐᵒᵖ G Γ Q φ ψ hexact hsurj _ γ m

/-- Each component comes from a continuous linear map of the compact quotient terms. -/
theorem chainFrobenius_continuous (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ Γ)
    (q : Q) (i : ℕ) :
    Continuous (show ((chain R G Γ Q φ ψ hexact hsurj M).X i).obj.V.toModule →
        ((chain R G Γ Q φ ψ hexact hsurj M).X i).obj.V.toModule from
      ((chainFrobenius R G Γ Q φ ψ hexact hsurj M q).f i).hom) :=
  (show _ →L[Rᵐᵒᵖ] _ from ((chain R G Γ Q φ ψ hexact hsurj M).X i).obj.ρ q).continuous

/-- Frobenius commutes with the actual resolution differential. -/
theorem chainFrobenius_comm (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ Γ)
    (q : Q) (i j : ℕ) :
    (chainFrobenius R G Γ Q φ ψ hexact hsurj M q).f i ≫
        (moduleChain R G Γ Q φ ψ hexact hsurj M).d i j =
      (moduleChain R G Γ Q φ ψ hexact hsurj M).d i j ≫
        (chainFrobenius R G Γ Q φ ψ hexact hsurj M q).f j :=
  (chainFrobenius R G Γ Q φ ψ hexact hsurj M q).comm i j

@[simp] theorem chainFrobenius_one (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ Γ) :
    chainFrobenius R G Γ Q φ ψ hexact hsurj M 1 = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext i
  simp only [chainFrobenius_f, map_one, HomologicalComplex.id_f]
  rfl

/-- Product order is the left-action order, hence reversed categorical composition. -/
theorem chainFrobenius_mul (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ Γ) (q r : Q) :
    chainFrobenius R G Γ Q φ ψ hexact hsurj M (q * r) =
      chainFrobenius R G Γ Q φ ψ hexact hsurj M r ≫
        chainFrobenius R G Γ Q φ ψ hexact hsurj M q := by
  apply HomologicalComplex.Hom.ext
  funext i
  simp only [HomologicalComplex.comp_f, chainFrobenius_f, map_mul]
  exact (NoncommCompactModule.forget Rᵐᵒᵖ).map_comp _ _

/-- Homological degree i is realized at cochain degree -i. -/
def cochain (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ Γ) :
    CochainComplex (ModuleCat.{u} Rᵐᵒᵖ) ℤ :=
  (moduleChain R G Γ Q φ ψ hexact hsurj M).extend ComplexShape.embeddingDownNat

/-- The specified degree is -i, with no compact-curve dimension shift. -/
def degreeIso (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ Γ) (i : ℕ) :
    (cochain R G Γ Q φ ψ hexact hsurj M).X (-(i : ℤ)) ≅
      (moduleChain R G Γ Q φ ψ hexact hsurj M).X i :=
  (moduleChain R G Γ Q φ ψ hexact hsurj M).extendXIso ComplexShape.embeddingDownNat rfl

/-- The same residual action, extended by zero in the specified degrees. -/
def cochainFrobenius (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ Γ) (q : Q) :
    cochain R G Γ Q φ ψ hexact hsurj M ⟶ cochain R G Γ Q φ ψ hexact hsurj M :=
  HomologicalComplex.extendMap (chainFrobenius R G Γ Q φ ψ hexact hsurj M q)
    ComplexShape.embeddingDownNat

/-- Extension preserves precisely the specified action in degree -i. -/
theorem cochainFrobenius_f (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ Γ)
    (q : Q) (i : ℕ) :
    (cochainFrobenius R G Γ Q φ ψ hexact hsurj M q).f (-(i : ℤ)) =
      (degreeIso R G Γ Q φ ψ hexact hsurj M i).hom ≫
        (chainFrobenius R G Γ Q φ ψ hexact hsurj M q).f i ≫
          (degreeIso R G Γ Q φ ψ hexact hsurj M i).inv :=
  HomologicalComplex.extendMap_f _ _ rfl

/-- Canonical homology comparison across the degree placement. -/
def degreeHomologyIso (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ Γ) (i : ℕ) :
    (cochain R G Γ Q φ ψ hexact hsurj M).homology (-(i : ℤ)) ≅
      (moduleChain R G Γ Q φ ψ hexact hsurj M).homology i :=
  (moduleChain R G Γ Q φ ψ hexact hsurj M).extendHomologyIso
    ComplexShape.embeddingDownNat rfl

/-- The degree comparison intertwines the maps induced on homology. -/
theorem degreeHomologyIso_frobenius (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ Γ)
    (q : Q) (i : ℕ) :
    HomologicalComplex.homologyMap (cochainFrobenius R G Γ Q φ ψ hexact hsurj M q)
        (-(i : ℤ)) ≫ (degreeHomologyIso R G Γ Q φ ψ hexact hsurj M i).hom =
      (degreeHomologyIso R G Γ Q φ ψ hexact hsurj M i).hom ≫
        HomologicalComplex.homologyMap (chainFrobenius R G Γ Q φ ψ hexact hsurj M q) i :=
  HomologicalComplex.extendHomologyIso_hom_naturality _ _ rfl

/-- The actual continuous residual homology complex in the derived module category. -/
def derived (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ Γ) :
    DerivedCategory (ModuleCat.{u} Rᵐᵒᵖ) :=
  DerivedCategory.Q.obj (cochain R G Γ Q φ ψ hexact hsurj M)

/-- Localize the specified residual Frobenius chain map. -/
def frobenius (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ Γ) (q : Q) :
    End (derived R G Γ Q φ ψ hexact hsurj M) :=
  DerivedCategory.Q.map (cochainFrobenius R G Γ Q φ ψ hexact hsurj M q)

@[simp] theorem frobenius_one (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ Γ) :
    frobenius R G Γ Q φ ψ hexact hsurj M 1 = 1 := by
  unfold frobenius cochainFrobenius
  rw [chainFrobenius_one, HomologicalComplex.extendMap_id]
  exact (DerivedCategory.Q (C := ModuleCat.{u} Rᵐᵒᵖ)).map_id _

theorem frobenius_mul (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ Γ) (q r : Q) :
    frobenius R G Γ Q φ ψ hexact hsurj M (q * r) =
      frobenius R G Γ Q φ ψ hexact hsurj M q *
        frobenius R G Γ Q φ ψ hexact hsurj M r := by
  unfold frobenius cochainFrobenius
  rw [chainFrobenius_mul, HomologicalComplex.extendMap_comp]
  exact (DerivedCategory.Q (C := ModuleCat.{u} Rᵐᵒᵖ)).map_comp _ _

/-- The residual group acts by the constructed derived endomorphisms. -/
def frobeniusAction (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ Γ) :
    Q →* End (derived R G Γ Q φ ψ hexact hsurj M) where
  toFun := frobenius R G Γ Q φ ψ hexact hsurj M
  map_one' := frobenius_one R G Γ Q φ ψ hexact hsurj M
  map_mul' := frobenius_mul R G Γ Q φ ψ hexact hsurj M

theorem frobenius_pow (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ Γ) (q : Q) (n : ℕ) :
    frobenius R G Γ Q φ ψ hexact hsurj M (q ^ n) =
      frobenius R G Γ Q φ ψ hexact hsurj M q ^ n :=
  (frobeniusAction R G Γ Q φ ψ hexact hsurj M).map_pow q n

/-- The chosen chain computes the existing left-derived residual coinvariant functor. -/
def homologyIso (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ Γ) (i : ℕ) :
    ((coinvariants R G Γ Q φ ψ hexact hsurj).leftDerived i).obj M ≅
      (chain R G Γ Q φ ψ hexact hsurj M).homology i :=
  (NoncommDualResolution.chosen R Γ M).isoLeftDerivedObj
    (coinvariants R G Γ Q φ ψ hexact hsurj) i

/-- The cochain action is definitionally the extension of the actual residual action. -/
theorem cochainFrobenius_eq (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ Γ) (q : Q) :
    cochainFrobenius R G Γ Q φ ψ hexact hsurj M q =
      HomologicalComplex.extendMap (chainFrobenius R G Γ Q φ ψ hexact hsurj M q)
        ComplexShape.embeddingDownNat := rfl

/-- The derived endomorphism is the localization of this very chain map. -/
theorem frobenius_eq (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ Γ) (q : Q) :
    frobenius R G Γ Q φ ψ hexact hsurj M q =
      DerivedCategory.Q.map (cochainFrobenius R G Γ Q φ ψ hexact hsurj M q) := rfl

end NoncommResidualHomology
