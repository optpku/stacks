/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Deformation.Difference

/-!
# Perturbations of morphisms between first-order thickenings

A map from pulled-back relative differentials to a conormal sheaf prescribes a unique
perturbation of a morphism between first-order thickenings.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.Deformation

variable {S X X' Y Y' : Scheme.{u}}

/-- A candidate perturbation has the prescribed restriction, conormal map, and difference
derivation determined by `θ`. -/
def IsPerturbation (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
    (a : X ⟶ Y) (a' : X' ⟶ Y') [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S] [a'.IsOver S]
    (sqA : CommSq a i j a')
    (θ : (Scheme.Modules.pullback a).obj Ω[(Y ↘ S).toShHom] ⟶
      Scheme.Hom.conormalSheaf i)
    (b' : X' ⟶ Y') : Prop :=
  b' ≫ (Y' ↘ S) = X' ↘ S ∧
    ∃ sqB : CommSq a i j b',
      Conormal.map sqA = Conormal.map sqB ∧
        ∀ (U : (Opens Y)ᵒᵖ)
          (x : (IsFirstOrderThickening.presentationSheaf j).obj.obj U),
          (presentationDifference sqB sqA).hom.app U x =
            (SquareZeroExtension.conormalInclusion
              (IsFirstOrderThickening.presentationProjection i)
              (IsFirstOrderThickening.presentationKernel_isSquareZero i)).hom.app
                ((Opens.map a.base).op.obj U)
                ((d[(Y ↘ S).toShHom].postcomp
                  (((Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv _ _) θ).val).d
                    ((IsFirstOrderThickening.presentationProjection j).hom.app U x))

/-- The defining conditions for a perturbation with prescribed differential map. -/
theorem isPerturbation_iff (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
    (a : X ⟶ Y) (a' : X' ⟶ Y') [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S] [a'.IsOver S]
    (sqA : CommSq a i j a')
    (θ : (Scheme.Modules.pullback a).obj Ω[(Y ↘ S).toShHom] ⟶
      Scheme.Hom.conormalSheaf i)
    (b' : X' ⟶ Y') :
    IsPerturbation S i j a a' sqA θ b' ↔
      b' ≫ (Y' ↘ S) = X' ↘ S ∧
        ∃ sqB : CommSq a i j b',
          Conormal.map sqA = Conormal.map sqB ∧
            ∀ (U : (Opens Y)ᵒᵖ)
              (x : (IsFirstOrderThickening.presentationSheaf j).obj.obj U),
              (presentationDifference sqB sqA).hom.app U x =
                (SquareZeroExtension.conormalInclusion
                  (IsFirstOrderThickening.presentationProjection i)
                  (IsFirstOrderThickening.presentationKernel_isSquareZero i)).hom.app
                    ((Opens.map a.base).op.obj U)
                    ((d[(Y ↘ S).toShHom].postcomp
                      (((Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv _ _) θ).val).d
                        ((IsFirstOrderThickening.presentationProjection j).hom.app U x)) := sorry

/-- A differential map uniquely determines a perturbation of a morphism between first-order
thickenings over the base scheme. -/
theorem existsUnique_perturbation (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
    (a : X ⟶ Y) (a' : X' ⟶ Y') [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S] [a'.IsOver S]
    (sqA : CommSq a i j a')
    (θ : (Scheme.Modules.pullback a).obj Ω[(Y ↘ S).toShHom] ⟶
      Scheme.Hom.conormalSheaf i) :
    ∃! b' : X' ⟶ Y', IsPerturbation S i j a a' sqA θ b' := sorry

end AlgebraicGeometry.Scheme.Hom.Deformation
