/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.SimplicialScheme.QCoh.Constant

/-!
# Quasi-coherent pullback to a Čech nerve
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.SimplicialObject.QCoh

/-- Pullback of quasi-coherent modules from the base scheme to its Čech nerve. -/
def cechPullback {X S : Scheme.{u}} (f : X ⟶ S) :
    Scheme.QCoh S ⥤ QCoh f.simplicialScheme :=
  constPullback S ⋙
    FullSubcategory.restrict (modulePullback (augmentation f))
      (modulePullback_le_inverseImage (augmentation f))

/-- The underlying module of Čech pullback is constant extension followed by
pullback along the augmentation. -/
theorem cechPullback_obj {X S : Scheme.{u}} (f : X ⟶ S) (G : Scheme.QCoh S) :
    ((cechPullback f).obj G).obj =
      (modulePullback (augmentation f)).obj ((constModulePullback S).obj G.obj) := rfl

/-- Pullback to the Čech nerve of a scheme morphism admitting a section is an equivalence
on quasi-coherent modules. -/
theorem cechPullback_isEquivalence {X S : Scheme.{u}} (f : X ⟶ S) [IsSplitEpi f] :
    (cechPullback f).IsEquivalence :=
  sorry

attribute [instance] cechPullback_isEquivalence

end AlgebraicGeometry.SimplicialObject.QCoh
