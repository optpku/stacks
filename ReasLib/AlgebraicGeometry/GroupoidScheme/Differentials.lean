/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Conormal
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Conormal.Splitting
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Sections

/-!
# Differentials of a groupoid scheme

This module constructs the canonical morphism from the source pullback of the conormal sheaf of
the identity section to the relative differentials of the target map of a groupoid scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme.Differentials

/-- The identity morphism of a groupoid scheme is an immersion. -/
theorem identity_isImmersion {S : Scheme.{u}} (G : GroupoidScheme S) :
    IsImmersion G.e.left :=
  Scheme.Hom.Section.isImmersion (by
    simpa using congrArg Over.Hom.left G.identity_source)

/-- The target map followed by the identity section and source map is again the target map. -/
theorem target_comp_identity_comp_source {S : Scheme.{u}} (G : GroupoidScheme S) :
    (G.t.left ≫ G.e.left) ≫ G.s.left = G.t.left := by
  have h_identity_source : G.e.left ≫ G.s.left = 𝟙 G.U.left := by
    simpa using congrArg Over.Hom.left G.identity_source
  simpa [Category.assoc] using congrArg (fun k ↦ G.t.left ≫ k) h_identity_source

/-- The groupoid identity law identifies the two relative-differentials objects used by the
identity-restriction comparison. -/
theorem identityRestrictionTransport_eq {S : Scheme.{u}} (G : GroupoidScheme S) :
    Ω[((G.t.left ≫ G.e.left) ≫ G.s.left).toShHom] = Ω[G.t.left.toShHom] := by
  simpa using congrArg (fun f ↦ Ω[f.toShHom]) (target_comp_identity_comp_source G)

/-- The transport from the relative differentials of `(t ≫ e) ≫ s` to those of `t`. -/
def identityRestrictionTransport {S : Scheme.{u}} (G : GroupoidScheme S) :
    Ω[((G.t.left ≫ G.e.left) ≫ G.s.left).toShHom] ⟶
      Ω[G.t.left.toShHom] :=
  eqToHom (identityRestrictionTransport_eq G)

/-- The pullback of the identity-section relative-differentials term along the target map,
transported to the target-relative differentials using the groupoid identity law. -/
def identityRestrictionComparison {S : Scheme.{u}} (G : GroupoidScheme S) :
    (Scheme.Modules.pullback G.t.left).obj
        ((Scheme.Modules.pullback G.e.left).obj Ω[G.s.left.toShHom]) ⟶
      Ω[G.t.left.toShHom] :=
  (Scheme.Modules.pullbackComp G.t.left G.e.left).hom.app Ω[G.s.left.toShHom] ≫
    Scheme.Hom.Conormal.Differentials.comparison (G.t.left ≫ G.e.left) G.s.left ≫
      identityRestrictionTransport G

/- The earlier identityRestrictionComparison is retained as the differential of `t ≫ e`.
It is not the translation comparison: for an additive group that differential is zero. -/

section Translation
variable {S : Scheme.{u}} (G : GroupoidScheme S)

/-- The right identity section `a ↦ (a, e(s(a)))` of multiplication. -/
def rightUnitSection : G.R ⟶ pullback G.s G.t :=
  pullback.lift (𝟙 G.R) (G.s ≫ G.e) (by simp [Category.assoc, G.identity_target])
/-- The second component of the right identity section. -/
theorem rightUnitSection_snd :
    (rightUnitSection G).left ≫ (pullback.snd G.s G.t).left = G.s.left ≫ G.e.left := by
  simpa [rightUnitSection] using congrArg Over.Hom.left
    (pullback.lift_snd (𝟙 G.R) (G.s ≫ G.e)
      (by simp [Category.assoc, G.identity_target]))
/-- Multiplication retracts its right identity section. -/
theorem rightUnitSection_mul : (rightUnitSection G).left ≫ G.c.left = 𝟙 G.R.left := by
  simpa [rightUnitSection] using congrArg Over.Hom.left
    (G.right_identity (𝟙 G.R) (by simp [Category.assoc, G.identity_target]))
/-- Multiplication and first projection form a cartesian square over the target. -/
theorem mulPB : IsPullback G.c.left (pullback.fst G.s G.t).left G.t.left G.t.left := by
  simpa using G.fstCompIsPullback.flip.map (Over.forget S)
/-- The defining composability square, with second projection horizontal. -/
theorem projPB : IsPullback (pullback.snd G.s G.t).left
    (pullback.fst G.s G.t).left G.t.left G.s.left := by
  simpa using G.fstSndIsPullback.flip.map (Over.forget S)
/-- Differential base change for the multiplication square. -/
def mulComparison : (RingedSpace.Hom.pullback G.c.left.toShHom).obj Ω[G.t.left.toShHom] ⟶
    Ω[(pullback.fst G.s G.t).left.toShHom] :=
  RingedSpace.Hom.Differentials.comparison
    ((mulPB G).toCommSq.map (Scheme.forgetToLocallyRingedSpace ⋙
      LocallyRingedSpace.forgetToSheafedSpace))
/-- Differential base change for the composability square. -/
def projComparison : (RingedSpace.Hom.pullback (pullback.snd G.s G.t).left.toShHom).obj
    Ω[G.t.left.toShHom] ⟶ Ω[(pullback.fst G.s G.t).left.toShHom] :=
  RingedSpace.Hom.Differentials.comparison
    ((projPB G).toCommSq.map (Scheme.forgetToLocallyRingedSpace ⋙
      LocallyRingedSpace.forgetToSheafedSpace))
/-- The multiplication differential comparison is an isomorphism. -/
theorem mulComparison_isIso : IsIso (mulComparison G) :=
  Scheme.RelativeDifferentials.comparison_isIso_of_isPullback (mulPB G)
/-- The projection differential comparison is an isomorphism. -/
theorem projComparison_isIso : IsIso (projComparison G) :=
  Scheme.RelativeDifferentials.comparison_isIso_of_isPullback (projPB G)
/-- Pulling multiplication base change along the right identity section. -/
def translationIso : Ω[G.t.left.toShHom] ≅
    (Scheme.Modules.pullback (rightUnitSection G).left).obj
      Ω[(pullback.fst G.s G.t).left.toShHom] :=
  ((Scheme.Modules.pullbackId G.R.left).app Ω[G.t.left.toShHom]).symm ≪≫
    ((Scheme.Modules.pullbackCongr (rightUnitSection_mul G)).app Ω[G.t.left.toShHom]).symm ≪≫
    ((Scheme.Modules.pullbackComp (rightUnitSection G).left G.c.left).app
      Ω[G.t.left.toShHom]).symm ≪≫
    (Scheme.Modules.pullback (rightUnitSection G).left).mapIso
      (@asIso _ _ _ _ (mulComparison G) (mulComparison_isIso G))
/-- Pulling projection base change along the right identity section. -/
def identityRestrictionIso :
    (Scheme.Modules.pullback G.s.left).obj
      ((Scheme.Modules.pullback G.e.left).obj Ω[G.t.left.toShHom]) ≅
    (Scheme.Modules.pullback (rightUnitSection G).left).obj
      Ω[(pullback.fst G.s G.t).left.toShHom] :=
  (Scheme.Modules.pullbackComp G.s.left G.e.left).app Ω[G.t.left.toShHom] ≪≫
    ((Scheme.Modules.pullbackCongr (rightUnitSection_snd G)).app Ω[G.t.left.toShHom]).symm ≪≫
    ((Scheme.Modules.pullbackComp (rightUnitSection G).left (pullback.snd G.s G.t).left).app
      Ω[G.t.left.toShHom]).symm ≪≫
    (Scheme.Modules.pullback (rightUnitSection G).left).mapIso
      (@asIso _ _ _ _ (projComparison G) (projComparison_isIso G))
end Translation

/-- The canonical morphism from the source pullback of the identity conormal sheaf to
target-relative differentials. The source/target convention is fixed by `s(a) = t(b)`
for composable pairs; the target-pullback formula in Stacks 04R9 requires this correction. -/
def conormalComparison {S : Scheme.{u}} (G : GroupoidScheme S) :
    (Scheme.Modules.pullback G.s.left).obj (Scheme.Hom.conormalSheaf G.e.left) ⟶
      Ω[G.t.left.toShHom] :=
  (Scheme.Modules.pullback G.s.left).map
      (Scheme.Hom.Conormal.Differentials.map G.e.left G.t.left) ≫
    (identityRestrictionIso G).hom ≫ (translationIso G).inv

/-- The comparison is the section conormal map followed by the two translation comparisons. -/
theorem conormalComparison_spec {S : Scheme.{u}} (G : GroupoidScheme S) :
    conormalComparison G =
      (Scheme.Modules.pullback G.s.left).map
          (Scheme.Hom.Conormal.Differentials.map G.e.left G.t.left) ≫
        (identityRestrictionIso G).hom ≫ (translationIso G).inv := rfl

/-- Translation identifies target-relative differentials with the source pullback of the
identity conormal sheaf. This construction does not require flatness. -/
def conormalComparisonIso {S : Scheme.{u}} (G : GroupoidScheme S) :
    (Scheme.Modules.pullback G.s.left).obj (Scheme.Hom.conormalSheaf G.e.left) ≅
      Ω[G.t.left.toShHom] :=
  (Scheme.Modules.pullback G.s.left).mapIso
    (@asIso _ _ _ _ (Scheme.Hom.Conormal.Differentials.map G.e.left G.t.left)
      (Scheme.Hom.Conormal.Differentials.map_isIso_of_section G.t.left G.e.left
        (by simpa using congrArg Over.Hom.left G.identity_target))) ≪≫
    identityRestrictionIso G ≪≫ (translationIso G).symm

/-- The isomorphism has the specified canonical comparison as its forward map. -/
theorem conormalComparisonIso_hom {S : Scheme.{u}} (G : GroupoidScheme S) :
    (conormalComparisonIso G).hom = conormalComparison G := rfl

/-- The groupoid conormal comparison is an epimorphism. -/
theorem conormalComparison_epi {S : Scheme.{u}} (G : GroupoidScheme S) :
    Epi (conormalComparison G) := by
  change Epi (conormalComparisonIso G).hom
  infer_instance

/-- Compatibility with the source-flat formulation of the groupoid comparison theorem. -/
theorem conormalComparison_isIso {S : Scheme.{u}} (G : GroupoidScheme S)
    [Flat G.s.left] : IsIso (conormalComparison G) := by
  change IsIso (conormalComparisonIso G).hom
  infer_instance

end AlgebraicGeometry.GroupoidScheme.Differentials
