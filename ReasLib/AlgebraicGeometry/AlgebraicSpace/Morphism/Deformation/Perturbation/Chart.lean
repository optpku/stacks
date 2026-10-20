/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Deformation.Perturbation.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.SchemeComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.Perturbation

/-!
# Differential parameters on actual scheme charts

The parameter derivation is evaluated on the target's actual etale charts. The module
base-change mate and the source conormal comparison carry its values to the source chart.
Restriction to scheme opens and the native Kähler descent then give the parameter consumed
by the actual scheme perturbation construction.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.Chart

variable {S : Scheme.{u}} {B X X' Y : AlgebraicSpace S}
variable {L L' W : Over S}
variable (iX : X ⟶ X') [IsFirstOrderThickening iX]
variable (iL : L ⟶ L') [AlgebraicGeometry.IsImmersion iL.left]
variable (a : X ⟶ Y) (l : L ⟶ W)
variable (qX : ofOver L ⟶ X) (qX' : ofOver L' ⟶ X') (qY : ofOver W ⟶ Y)
variable [Etale qY]
variable (sq : CommSq qX (ofOverMap l) a qY)
variable (sqI : CommSq qX (ofOverMap iL) iX qX')

/-- Base change and the actual conormal map carry the original pushed coefficient to the
source chart's pushed conormal module. The square need only commute. -/
def coefficientMap :
    (Modules.restrictFunctor qY).obj ((Modules.pushforward a).obj (Hom.conormalSheaf iX)) ⟶
      (Modules.pushforward (ofOverMap l)).obj (Hom.conormalSheaf (ofOverMap iL)) :=
  (Modules.restrictFunctorIsoPullback qY).hom.app
      ((Modules.pushforward a).obj (Hom.conormalSheaf iX)) ≫
    (Modules.baseChange sq.w).app (Hom.conormalSheaf iX) ≫
    (Modules.pushforward (ofOverMap l)).map (Hom.Conormal.map sqI)

/-- Restrict the coefficient comparison to scheme opens, then use the specified
direct-image and algebraic-space/scheme conormal comparisons. -/
def schemeCoefficientMap :
    (Modules.restrictToScheme W).obj
        ((Modules.restrictFunctor qY).obj ((Modules.pushforward a).obj (Hom.conormalSheaf iX))) ⟶
      (Scheme.Modules.pushforward l.left).obj (Scheme.Hom.conormalSheaf iL.left) :=
  (Modules.restrictToScheme W).map (coefficientMap iX iL a l qX qX' qY sq sqI) ≫
    pushforwardComparisonApp l (Hom.conormalSheaf (ofOverMap iL)) ≫
    (Scheme.Modules.pushforward l.left).map (Hom.Conormal.restrictToSchemeIsoHom iL)

variable (p : Y ⟶ B)
variable (D : Hom.derivations p ((Modules.pushforward a).obj (Hom.conormalSheaf iX)))

/-- Evaluate the given derivation on an actual target open chart and send its value through
the constructed coefficient maps. The function acts on the original ring sections. -/
def derivationSection (V : W.left.Opens) (r : W.left.presheaf.obj (op V)) :
    ((Scheme.Modules.pushforward l.left).obj (Scheme.Hom.conormalSheaf iL.left)).val.obj
      (op V) :=
  let U := siteObject W V
  let t : (commStructureSheaf Y).obj.obj (op ((Modules.restrictPostcompose qY).obj U)) :=
    ((@Scheme.restrictFunctorΓ W.left).inv.app (op V)).hom r
  let d := D.d t
  let restricted :
      ((Modules.restrictFunctor qY).obj
        ((Modules.pushforward a).obj (Hom.conormalSheaf iX))).val.obj (op U) :=
    ((Modules.restrictAppIso ((Modules.pushforward a).obj (Hom.conormalSheaf iX)) qY U).inv).hom d
  ((schemeCoefficientMap iX iL a l qX qX' qY sq sqI).val.app (op V)).hom
    ((sectionEquiv W _ V).symm restricted)

/-- The evaluated chart functions preserve zero and addition, satisfy the Leibniz
rule, commute with restriction, and vanish on the inverse-image base coefficients. -/
private theorem derivation_laws :
    let M := (Scheme.Modules.pushforward l.left).obj (Scheme.Hom.conormalSheaf iL.left)
    let R := W.left.sheaf.obj
    let φ := RingedSpace.Hom.inverseImageStructureSheafHomComm W.hom.toShHom
    let d : ∀ V : W.left.Opensᵒᵖ, R.obj V → M.val.obj V :=
      fun V r ↦ derivationSection iX iL a l qX qX' qY sq sqI p D V.unop r
    (∀ V, d V 0 = 0) ∧
    (∀ V r s, d V (r + s) = d V r + d V s) ∧
    (∀ V r s, d V (r * s) = r • d V s + s • d V r) ∧
    (∀ {V Z : W.left.Opensᵒᵖ} (f : V ⟶ Z) (r : R.obj V),
      d Z (R.map f r) = M.val.map f (d V r)) ∧
    (∀ (V : W.left.Opensᵒᵖ)
      (r : ((TopCat.Sheaf.pullback CommRingCat.{u} W.hom.base).obj S.toRingedSpace.sheaf).obj.obj V),
      d V (φ.hom.app V r) = 0) := sorry

-- The canonical chart and coefficient comparisons yield deeply nested definitional equalities.
set_option maxRecDepth 4096 in
/-- The evaluated chart functions form a derivation relative to the scheme base. -/
def derivation :
    RingedSpace.Hom.derivations W.hom.toShHom
      ((Scheme.Modules.pushforward l.left).obj (Scheme.Hom.conormalSheaf iL.left)) where
  d {U} :=
    { toFun := derivationSection iX iL a l qX qX' qY sq sqI p D U.unop
      map_zero' := by exact (derivation_laws iX iL a l qX qX' qY sq sqI p D).1 U
      map_add' := by exact (derivation_laws iX iL a l qX qX' qY sq sqI p D).2.1 U }
  d_mul {U} r s := by
    dsimp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    exact (derivation_laws iX iL a l qX qX' qY sq sqI p D).2.2.1 U r s
  d_map {U V} f r := by
    dsimp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    exact (derivation_laws iX iL a l qX qX' qY sq sqI p D).2.2.2.1 f r
  d_app {U} r := by
    dsimp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    exact (derivation_laws iX iL a l qX qX' qY sq sqI p D).2.2.2.2 U r

/-- The actual scheme-chart differential parameter is obtained by native Kähler descent
of the evaluated chart derivation, then the scheme pullback/pushforward adjunction. -/
def parameter :
    (Scheme.Modules.pullback l.left).obj (RingedSpace.Hom.differentials W.hom.toShHom) ⟶
      Scheme.Hom.conormalSheaf iL.left :=
  ((Scheme.Modules.pullbackPushforwardAdjunction l.left).homEquiv _ _).symm
    (RingedSpace.Hom.differentialDesc W.hom.toShHom
      (derivation iX iL a l qX qX' qY sq sqI p D))

/-- Perturb the supplied actual scheme-chart map using the descended chart parameter.
The local map is the explicit scheme square-zero presentation construction. -/
def perturb {W' : Over S} (iW : W ⟶ W') (l' : L' ⟶ W')
    [AlgebraicGeometry.IsFirstOrderThickening iL.left]
    [AlgebraicGeometry.IsFirstOrderThickening iW.left]
    (sqL : CommSq l iL iW l') : L' ⟶ W' := by
  -- Local instance justification (defeq pin): use the structural map L.hom of the stored Over S object L.
  letI : L.left.Over S := ⟨L.hom⟩
  -- Local instance justification (defeq pin): use the structural map L'.hom of the stored Over S object L'.
  letI : L'.left.Over S := ⟨L'.hom⟩
  -- Local instance justification (defeq pin): use the structural map W.hom of the stored Over S object W.
  letI : W.left.Over S := ⟨W.hom⟩
  -- Local instance justification (defeq pin): use the structural map W'.hom of the stored Over S object W'.
  letI : W'.left.Over S := ⟨W'.hom⟩
  -- Local instance justification (defeq pin): use Over.w iL for the stored Over S arrow iL.
  letI : iL.left.IsOver S := ⟨Over.w iL⟩
  -- Local instance justification (defeq pin): use Over.w iW for the stored Over S arrow iW.
  letI : iW.left.IsOver S := ⟨Over.w iW⟩
  -- Local instance justification (defeq pin): use Over.w l for the stored Over S arrow l.
  letI : l.left.IsOver S := ⟨Over.w l⟩
  exact Over.homMk
    (Scheme.Hom.Deformation.perturbHom S iL.left iW.left l.left l'.left
      (ofOverSqLeft sqL) (parameter iX iL a l qX qX' qY sq sqI p D)) sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.Chart
