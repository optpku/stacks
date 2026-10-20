/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.LocalHomDirectImage
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FieldGeometricAdjunction

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace FieldHomSectionsComparison
variable {k : Type u} [Field k]
variable {A R : Type (u + 1)} [CommRing A] [Ring R]
variable (h : A →+* R) (hc : ∀ (a : A) (r : R), h a * r = r * h a)
variable (P : SchemeOverField k) [CompactSpace P.left] [QuasiSeparatedSpace P.left]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} R)]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ)]
variable [∀ Y : Scheme.{u}, Y.smallEtaleTopology.HasSheafCompose (NoncommLocalHom.modules h)]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R),
  (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Rᵐᵒᵖ),
  (smallEtalePullback f).op.HasLeftKanExtension F]
variable (B : DiscreteModuleCat R Gal(AlgebraicClosure k/k))
variable (J : Sheaf P.left.smallEtaleTopology (ModuleCat.{u + 1} A))

abbrev pulledSource := (FieldGeometricAdjunction.pullback R P).obj B
abbrev geometricHom := NoncommLocalHom.obj h hc P.left (pulledSource P B) J

/-- The field-site internal Hom retains the smooth residual action even for
infinite inputs; it is not falsely replaced by all algebraic Hom functions. -/
def fieldHom := NoncommLocalHom.obj h hc (Spec (CommRingCat.of k))
  ((FieldModuleDescent.inverse k R).obj B) ((LocalHomDirectImage.pushforward P.hom A).obj J)

/-- Actual closed-adjunction section comparison in the residual Galois category:
invert geometric stalk/direct-image continuity, then apply the explicit local
unit/evaluation map over the field and its genuine stalk action. -/
def iso : (NoncommGeometricSource.discreteSections Rᵐᵒᵖ P).obj (geometricHom h hc P B J) ≅
    (FieldModuleDescent.forward k Rᵐᵒᵖ).obj (fieldHom h hc P B J) :=
  (asIso ((FieldGeometricAdjunction.comparison Rᵐᵒᵖ P).app (geometricHom h hc P B J))).symm ≪≫
  (FieldModuleDescent.forward k Rᵐᵒᵖ).mapIso
    (LocalHomDirectImage.iso h hc P.hom ((FieldModuleDescent.inverse k R).obj B) J)

end FieldHomSectionsComparison
