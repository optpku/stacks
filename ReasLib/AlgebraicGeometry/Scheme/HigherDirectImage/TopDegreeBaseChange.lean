module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal

/-!
# Top-Degree Base Change

This module records the vanishing, projection-formula, and base-change conditions satisfied by
higher direct images in the highest potentially nonzero degree.
-/

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.HigherDirectImage

variable {X Y : Scheme.{u}}

/-- Higher direct images of every quasicoherent module along `f` vanish in degrees above `d`. -/
def VanishesAbove (f : X ⟶ Y) (d : ℕ) : Prop :=
  ∀ (ℱ : X.Modules) [ℱ.IsQuasicoherent] (i : ℕ), d < i →
    IsZero (higherDirectImageModule f.toShHom ℱ i)

/-- Vanishing above `d` persists after every cartesian base change of `f`. -/
def VanishesAboveAfterBaseChange (f : X ⟶ Y) (d : ℕ) : Prop :=
  ∀ {X' Y' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y),
    IsPullback g' f' f g → VanishesAbove f' d

/-- After every cartesian base change of `f`, the degree-`d` higher direct image satisfies the
projection formula for quasicoherent modules. -/
def ProjectionFormulaAfterBaseChange (f : X ⟶ Y) (d : ℕ) : Prop :=
  ∀ {X' Y' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y),
    IsPullback g' f' f g → ∀ (ℱ' : X'.Modules) [ℱ'.IsQuasicoherent]
      (𝒢' : Y'.Modules) [𝒢'.IsQuasicoherent],
      IsIsomorphic
        (higherDirectImageModule f'.toShHom
          (ℱ' ⊗ (Scheme.Modules.pullback f').obj 𝒢') d)
        (higherDirectImageModule f'.toShHom ℱ' d ⊗ 𝒢')

/-- After every cartesian base change of `f`, the degree-`d` higher direct image of a
quasicoherent module commutes with every further cartesian base change. -/
def CommutesWithBaseChangeAfterBaseChange (f : X ⟶ Y) (d : ℕ) : Prop :=
  ∀ {X' Y' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y),
    IsPullback g' f' f g → ∀ (ℱ' : X'.Modules) [ℱ'.IsQuasicoherent]
      {X'' Y'' : Scheme.{u}} (h' : X'' ⟶ X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ Y'),
      IsPullback h' f'' f' h →
      IsIsomorphic
        ((Scheme.Modules.pullback h).obj (higherDirectImageModule f'.toShHom ℱ' d))
        (higherDirectImageModule f''.toShHom ((Scheme.Modules.pullback h').obj ℱ') d)

/-- A morphism satisfies top-degree base change in degree `d` if its source and target are
quasi-compact and quasi-separated, its higher direct images vanish above `d`, and the
vanishing, projection formula, and degree-`d` base-change compatibility persist after arbitrary
cartesian base change. -/
def TopDegreeBaseChange (f : X ⟶ Y) (d : ℕ) : Prop :=
  CompactSpace X.carrier ∧ QuasiSeparatedSpace X.carrier ∧
    CompactSpace Y.carrier ∧ QuasiSeparatedSpace Y.carrier ∧
    VanishesAbove f d ∧ VanishesAboveAfterBaseChange f d ∧
    ProjectionFormulaAfterBaseChange f d ∧ CommutesWithBaseChangeAfterBaseChange f d

/-- The top-degree base-change property is exactly its compactness, separation, vanishing,
projection-formula, and further-base-change conditions. -/
theorem topDegreeBaseChange_iff (f : X ⟶ Y) (d : ℕ) :
    TopDegreeBaseChange f d ↔
      CompactSpace X.carrier ∧ QuasiSeparatedSpace X.carrier ∧
        CompactSpace Y.carrier ∧ QuasiSeparatedSpace Y.carrier ∧
        VanishesAbove f d ∧ VanishesAboveAfterBaseChange f d ∧
        ProjectionFormulaAfterBaseChange f d ∧ CommutesWithBaseChangeAfterBaseChange f d :=
  Iff.rfl

/-- For a morphism between quasi-compact and quasi-separated schemes, vanishing of
quasicoherent higher direct images above `d` implies the complete top-degree base-change
property in degree `d`. -/
theorem topDegreeBaseChange_of_vanishesAbove
    (f : X ⟶ Y) (d : ℕ)
    [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
    [CompactSpace Y.carrier] [QuasiSeparatedSpace Y.carrier]
    (hvanish : VanishesAbove f d) : TopDegreeBaseChange f d := sorry

end AlgebraicGeometry.Scheme.HigherDirectImage
