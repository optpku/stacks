/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Generator.Basic
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.Adjunction
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.Dual
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.BraidedClosed
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.Naturality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Biduality for a right internal Hom

This file extends the variance-only dual functors from `RightInternalHom.Dual` with the
canonical map to the double dual. The construction is independent of modules and sheaves;
a coseparator makes every component of the bidual map monic.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open MonoidalCategory Opposite
open scoped CategoryTheory.RightInternalHom

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

namespace RightInternalHom

variable (H : RightInternalHom C)

set_option backward.isDefEq.respectTransparency false

/-- The component at `X` of the canonical map to the `J`-bidual. -/
@[stacks 01DS "bidual map"]
def toBidualApp (J X : C) : X ⟶ (H.bidualFunctor J).obj X :=
  H.curry ((β_ X (H.dual J X)).hom ≫ H.ev X J)

/-- The canonical bidual components are natural in `X`. -/
theorem toBidualApp_naturality (J : C) {X Y : C} (f : X ⟶ Y) :
    (𝟭 C).map f ≫ H.toBidualApp J Y =
      H.toBidualApp J X ≫ (H.bidualFunctor J).map f := by
  change f ≫ H.curry ((β_ Y (Y ⟶[H]ᵣ J)).hom ≫ H.ev Y J) =
    H.curry ((β_ X (X ⟶[H]ᵣ J)).hom ≫ H.ev X J) ≫
      (H.hom.map (((H.hom.map f.op).app J).op)).app J
  apply H.uncurry_injective
  rw [H.uncurry_natural_left, H.uncurry_natural_parameter]
  simp only [H.uncurry_curry]
  rw [BraidedCategory.braiding_naturality_left_assoc]
  rw [← H.ev_natural_parameter f]
  rw [← BraidedCategory.braiding_naturality_right_assoc]

/-- The canonical natural transformation from the identity functor to double dualization
with values in `J`. -/
@[stacks 01DS "bidual transformation"]
def toBidual (J : C) : 𝟭 C ⟶ H.bidualFunctor J where
  app X := H.toBidualApp J X
  naturality X Y f := H.toBidualApp_naturality J (X := X) (Y := Y) f

/-- Evaluation of a `J`-bidual element at a morphism `f : X ⟶ J`. -/
def evaluateAt (J : C) {X : C} (f : X ⟶ J) :
    (H.bidualFunctor J).obj X ⟶ J :=
  (ρ_ ((H.bidualFunctor J).obj X)).inv ≫
    ((H.bidualFunctor J).obj X ◁ H.curry ((λ_ X).hom ≫ f)) ≫
      H.ev (H.dual J X) J

/-- Evaluating the canonical bidual map at `f` recovers `f`. -/
@[reassoc]
theorem toBidual_app_comp_evaluateAt (J : C) {X : C} (f : X ⟶ J) :
    (H.toBidual J).app X ≫ H.evaluateAt J f = f := by
  change H.curry ((β_ X (X ⟶[H]ᵣ J)).hom ≫ H.ev X J) ≫
    (ρ_ ((X ⟶[H]ᵣ J) ⟶[H]ᵣ J)).inv ≫
      (((X ⟶[H]ᵣ J) ⟶[H]ᵣ J) ◁ H.curry ((λ_ X).hom ≫ f)) ≫
        H.ev (X ⟶[H]ᵣ J) J = f
  rw [MonoidalCategory.rightUnitor_inv_naturality_assoc]
  rw [← MonoidalCategory.whisker_exchange_assoc]
  rw [← H.uncurry_eq]
  rw [H.uncurry_curry]
  rw [BraidedCategory.braiding_naturality_right_assoc]
  rw [rightUnitor_inv_braiding_assoc]
  rw [← H.uncurry_eq, H.uncurry_curry]
  simp

/-- If `J` is a coseparator, every component of the canonical map to the
`J`-bidual is monic. -/
@[stacks 01DS "monomorphism criterion"]
theorem mono_toBidual_of_isCoseparator (J X : C) (hJ : IsCoseparator J) :
    Mono ((H.toBidual J).app X) := by
  change Mono (H.toBidualApp J X)
  constructor
  intro Z f g hfg
  apply hJ.def f g
  intro h
  rw [← H.toBidual_app_comp_evaluateAt J h]
  simpa only [toBidual, Category.assoc] using
    congrArg (fun k => k ≫ H.evaluateAt J h) hfg

end RightInternalHom

end CategoryTheory
