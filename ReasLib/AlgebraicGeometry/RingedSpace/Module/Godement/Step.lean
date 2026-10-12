/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Skyscraper
public import ReasLib.CategoryTheory.Adjunction.Pi
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The Godement monad on module sheaves

For a ringed space `X`, pullback to every point is left adjoint to the corresponding
skyscraper-module functor.  Taking the product of these right adjoints gives one adjunction
between `X.Modules` and the category of point-indexed stalk modules.  Its induced monad is the
canonical Godement step.  Keeping the adjunction and monad as the data owners supplies the unit
and multiplication needed by the functorial cosimplicial resolution.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Godement

/-- The category of families of modules over all stalk rings of `X`. -/
@[stacks 0FKS "point-indexed stalk modules"]
abbrev Discrete (X : RingedSpace.{u}) :=
  ∀ x : X, ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))

/-- Pull an `𝒪_X`-module back to every point of `X`. -/
@[stacks 0FKS "pullback to the discrete family of points"]
noncomputable abbrev toDiscrete (X : RingedSpace.{u}) : X.Modules ⥤ Discrete X :=
  Functor.pi' fun x : X ↦ RingedSpace.Module.pointPullbackFunctor x

/-- Form the product of the skyscraper modules associated to a family of stalk modules. -/
@[stacks 0FKS "product of skyscraper modules"]
noncomputable abbrev fromDiscrete (X : RingedSpace.{u}) : Discrete X ⥤ X.Modules :=
  Functor.pi (fun x : X ↦ RingedSpace.Module.Skyscraper.functor x) ⋙
    Limits.Pi.functor X

/-- Pullback to every point is left adjoint to the product of the corresponding skyscraper
module functors. -/
@[stacks 0FKS "Godement point-family adjunction"]
noncomputable def adjunction (X : RingedSpace.{u}) :
    toDiscrete X ⊣ fromDiscrete X :=
  CategoryTheory.Adjunction.pi
    (fun x : X ↦ RingedSpace.Module.pointPullbackFunctor x)
    (fun x : X ↦ RingedSpace.Module.Skyscraper.functor x)
    (fun x : X ↦ RingedSpace.Module.Skyscraper.adjunction x)

/-- The Godement monad induced by pullback to all points and the product of skyscraper modules. -/
@[stacks 0FKS "Godement monad"]
noncomputable def monad (X : RingedSpace.{u}) : Monad X.Modules :=
  (adjunction X).toMonad

/-- The underlying Godement step endofunctor. -/
@[stacks 0FKS "Godement step"]
noncomputable abbrev step (X : RingedSpace.{u}) : X.Modules ⥤ X.Modules :=
  monad X

/-- The Godement step is additive; this is the canonical instance used when it is applied
degreewise to complexes. -/
@[stacks 0FKS "additivity of the Godement step"]
noncomputable instance step_additive (X : RingedSpace.{u}) :
    (step X).Additive := sorry

/-- The canonical Godement unit `𝟭 X.Modules ⟶ step X`. -/
@[stacks 0FKS "Godement unit"]
noncomputable abbrev unit (X : RingedSpace.{u}) : 𝟭 X.Modules ⟶ step X :=
  (monad X).η

/-- The canonical multiplication of two consecutive Godement steps. -/
@[stacks 0FKS "Godement multiplication"]
noncomputable abbrev multiplication (X : RingedSpace.{u}) :
    step X ⋙ step X ⟶ step X :=
  (monad X).μ

/-- The pointwise value of `toDiscrete X` is the canonical point-pullback module. -/
@[simp]
theorem toDiscrete_obj_apply (X : RingedSpace.{u}) (ℱ : X.Modules) (x : X) :
    (toDiscrete X).obj ℱ x = (RingedSpace.Module.pointPullbackFunctor x).obj ℱ := sorry

/-- The right adjoint sends a family of stalk modules to the product of its skyscraper modules. -/
theorem fromDiscrete_obj (X : RingedSpace.{u}) (M : Discrete X) :
    (fromDiscrete X).obj M =
      ∏ᶜ fun x : X ↦ (RingedSpace.Module.Skyscraper.functor x).obj (M x) := sorry

/-- A Godement step is the product of the skyscraper modules of all point pullbacks. -/
theorem step_obj (X : RingedSpace.{u}) (ℱ : X.Modules) :
    (step X).obj ℱ =
      ∏ᶜ fun x : X ↦
        (RingedSpace.Module.Skyscraper.functor x).obj
          ((RingedSpace.Module.pointPullbackFunctor x).obj ℱ) := sorry

/-- Projecting the Godement unit to the `x`-th skyscraper factor recovers the unit of the
point-pullback/skyscraper adjunction. -/
@[reassoc (attr := simp)]
theorem unit_app_π (X : RingedSpace.{u}) (ℱ : X.Modules) (x : X) :
    (unit X).app ℱ ≫
        Limits.Pi.π
          (fun y : X ↦
            (RingedSpace.Module.Skyscraper.functor y).obj
              ((RingedSpace.Module.pointPullbackFunctor y).obj ℱ)) x =
      (RingedSpace.Module.Skyscraper.adjunction x).unit.app ℱ := sorry

end AlgebraicGeometry.RingedSpace.Godement
