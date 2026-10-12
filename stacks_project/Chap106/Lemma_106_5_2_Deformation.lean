/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import stacks_project.Chap100.Definition_100_8_1_Mono
public import stacks_project.Chap100.Definition_100_9_1_Immersion
public import stacks_project.Chap101.Definition_101_10_1_Integral
public import stacks_project.Chap101.Definition_101_23_2_LocallyQuasiFinite
public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType
public import stacks_project.Chap101.Lemma_101_25_5_Flat
public import stacks_project.Chap101.Lemma_101_36_4_Etale
public import stacks_project.Chap101.Lemma_101_36_4_Unramified
public import stacks_project.Chap103.«103_15_1_1_Smooth»
public import stacks_project.Chap106.Definition_106_3_1_Hom
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation
public import stacks_project.Chap106.Lemma_106_5_2_Syntomic

/-!
# Morphism properties in cartesian deformations of algebraic stacks

This file records invariance of morphism properties of algebraic stacks in
2-commutative triangles of thickenings whose vertical squares are 2-fibre
products, with the ambient target locally of finite type and the ambient
source flat and locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsThickening

variable {S : Scheme.{u}} {X X' Y Y' B B' : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
variable [AlgebraicStack B] [AlgebraicStack B']
variable {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iB : B ⟶ B'}
variable {f : X ⟶ Y} {f' : X' ⟶ Y'}
variable {pX : X ⟶ B} {pX' : X' ⟶ B'} {pY : Y ⟶ B} {pY' : Y' ⟶ B'}
variable [thickeningX : IsThickening iX] [thickeningY : IsThickening iY]
variable [thickeningB : IsThickening iB]
variable [finiteTypeY' : LocallyOfFiniteType pY']
variable [flatX' : Flat pX'] [finitePresentationX' : LocallyOfFinitePresentation pX']
variable (sq : Hom iX iY f f') (hX : Hom iX iB pX pX') (hY : Hom iY iB pY pY')
variable (triangle : f ≫ pY ≅ pX) (triangle' : f' ≫ pY' ≅ pX')
variable (pullbackX : (⟨X, pX, iX, hX.w⟩ : PseudoPullbackCone iB pX').IsBilimit)
variable (pullbackY : (⟨Y, pY, iY, hY.w⟩ : PseudoPullbackCone iB pY').IsBilimit)

include thickeningX thickeningY thickeningB finiteTypeY' flatX' finitePresentationX'
include sq hX hY triangle triangle' pullbackX pullbackY

/-- In a 2-commutative triangle of thickenings of algebraic stacks whose
vertical squares are 2-fibre products, the closed-fiber morphism is flat if
and only if the ambient morphism is flat, under the stated finiteness
hypotheses. -/
theorem flat_iff : Flat f ↔ Flat f' := sorry

/-- In a 2-commutative triangle of thickenings of algebraic stacks whose
vertical squares are 2-fibre products, the closed-fiber morphism is an
isomorphism of algebraic stacks if and only if the ambient morphism is an
isomorphism, i.e. the underlying based functors are equivalences, under the
stated finiteness hypotheses. -/
theorem isIso_iff :
    (toBasedFunctor f).IsEquivalence ↔ (toBasedFunctor f').IsEquivalence := sorry

/-- In a 2-commutative triangle of thickenings of algebraic stacks whose
vertical squares are 2-fibre products, the closed-fiber morphism is an open
immersion if and only if the ambient morphism is an open immersion, under the
stated finiteness hypotheses. -/
theorem openImmersion_iff :
    Groupoids.Hom.OpenImmersion f ↔ Groupoids.Hom.OpenImmersion f' := sorry

/-- In a 2-commutative triangle of thickenings of algebraic stacks whose
vertical squares are 2-fibre products, the closed-fiber morphism is a
monomorphism if and only if the ambient morphism is a monomorphism, under the
stated finiteness hypotheses. -/
theorem mono_iff : Groupoids.Hom.Mono f ↔ Groupoids.Hom.Mono f' := sorry

/-- In a 2-commutative triangle of thickenings of algebraic stacks whose
vertical squares are 2-fibre products, the closed-fiber morphism is locally
quasi-finite if and only if the ambient morphism is locally quasi-finite,
under the stated finiteness hypotheses. -/
theorem locallyQuasiFinite_iff :
    LocallyQuasiFinite f ↔ LocallyQuasiFinite f' := sorry

/-- In a 2-commutative triangle of thickenings of algebraic stacks whose
vertical squares are 2-fibre products, the closed-fiber morphism is syntomic
if and only if the ambient morphism is syntomic, under the stated finiteness
hypotheses. -/
theorem syntomic_iff : Syntomic f ↔ Syntomic f' := sorry

/-- In a 2-commutative triangle of thickenings of algebraic stacks whose
vertical squares are 2-fibre products, the closed-fiber morphism is smooth if
and only if the ambient morphism is smooth, under the stated finiteness
hypotheses. -/
theorem smooth_iff : Smooth f ↔ Smooth f' := sorry

/-- In a 2-commutative triangle of thickenings of algebraic stacks whose
vertical squares are 2-fibre products, the closed-fiber morphism is
unramified if and only if the ambient morphism is unramified, under the
stated finiteness hypotheses. -/
theorem unramified_iff : Unramified f ↔ Unramified f' := sorry

/-- In a 2-commutative triangle of thickenings of algebraic stacks whose
vertical squares are 2-fibre products, the closed-fiber morphism is étale if
and only if the ambient morphism is étale, under the stated finiteness
hypotheses. -/
theorem etale_iff : Etale f ↔ Etale f' := sorry

/-- In a 2-commutative triangle of thickenings of algebraic stacks whose
vertical squares are 2-fibre products, the closed-fiber morphism is finite if
and only if the ambient morphism is finite, under the stated finiteness
hypotheses. -/
theorem isFinite_iff : IsFinite f ↔ IsFinite f' := sorry

end AlgebraicGeometry.AlgebraicStack.IsThickening
