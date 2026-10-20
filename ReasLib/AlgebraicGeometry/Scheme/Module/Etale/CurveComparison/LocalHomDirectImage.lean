/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommLocalHom
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommGeometricSource

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace LocalHomDirectImage
variable {A R : Type (u + 1)} [CommRing A] [Ring R]
variable (h : A →+* R) (hc : ∀ (a : A) (r : R), h a * r = r * h a)
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [X.smallEtaleTopology.HasSheafCompose (NoncommLocalHom.modules h)]
variable [Y.smallEtaleTopology.HasSheafCompose (NoncommLocalHom.modules h)]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} R)]
variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} R)]
variable [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R, (smallEtalePullback f).op.HasLeftKanExtension F]
variable (B : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
variable (J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))

abbrev pullback := (smallEtalePullback f).sheafPullback (ModuleCat.{u + 1} R)
  Y.smallEtaleTopology X.smallEtaleTopology

def pushforward (S : Type (u + 1)) [Ring S] :=
  (smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u + 1} S)
    Y.smallEtaleTopology X.smallEtaleTopology

abbrev source := (pushforward f Rᵐᵒᵖ).obj (NoncommLocalHom.obj h hc X ((pullback (R := R) f).obj B) J)
abbrev target := NoncommLocalHom.obj h hc Y B ((pushforward f A).obj J)

/-- The closed adjunction's actual section map: pull a source section through
the module inverse-image unit, then evaluate the supplied local transformation
on the explicitly pulled-back slice chart. -/
def sectionMap (U : Y.Etaleᵒᵖ) (α : (source h hc f B J).obj.obj U) :
    (target h hc f B J).obj.obj U :=
  { app := fun V ↦
      (NoncommLocalHom.modules h).map
        (((smallEtalePullback_sheafAdjunction f (ModuleCat.{u + 1} R)).unit.app B).hom.app (op V.unop.left)) ≫
      α.app (op (Over.mk ((smallEtalePullback f).map V.unop.hom)))
    naturality := by sorry }

/-- This is a morphism of actual right-R sheaves, not a chosen closed-Hom iso. -/
def comparison : source h hc f B J ⟶ target h hc f B J :=
  ObjectProperty.homMk
    { app := fun U ↦ ConcreteCategory.ofHom (C := ModuleCat.{u + 1} Rᵐᵒᵖ)
        { toFun := sectionMap h hc f B J U
          map_add' := by sorry
          map_smul' := by sorry }
      naturality := by sorry }

/-- The usual closed inverse-image/direct-image adjunction proves this
specified map invertible. No flatness or finite-field assumption is needed. -/
instance comparison_isIso : IsIso (comparison h hc f B J) := by sorry

def iso : source h hc f B J ≅ target h hc f B J :=
  @asIso _ _ _ _ (comparison h hc f B J) (comparison_isIso h hc f B J)

end LocalHomDirectImage
