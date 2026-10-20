/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Unramified
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Thickening.Hom
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Syntomic

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
variable (pullbackX : PseudoPullbackCone.IsBilimit
  (⟨X, pX, iX, hX.w⟩ : PseudoPullbackCone iB pX'))
variable (pullbackY : PseudoPullbackCone.IsBilimit
  (⟨Y, pY, iY, hY.w⟩ : PseudoPullbackCone iB pY'))

include thickeningX thickeningY thickeningB finiteTypeY' flatX' finitePresentationX'
include sq hX hY triangle triangle' pullbackX pullbackY

/-- In a 2-commutative triangle of thickenings of algebraic stacks with
cartesian vertical squares, suppose the ambient target is locally of finite
type over the ambient base and the ambient source is flat and locally of
finite presentation over that base. Then the closed-fiber morphism is
flat if and only if the ambient morphism is flat. -/
theorem flat_iff : Flat f ↔ Flat f' := sorry

/-- In a 2-commutative triangle of thickenings of algebraic stacks with
cartesian vertical squares, suppose the ambient target is locally of finite
type over the ambient base and the ambient source is flat and locally of
finite presentation over that base. Then the closed-fiber morphism is
an isomorphism of algebraic stacks if and only if the ambient morphism is an isomorphism of algebraic stacks.
Here isomorphism means equivalence of the underlying based functors. -/
theorem isIso_iff :
    (toBasedFunctor f).IsEquivalence ↔ (toBasedFunctor f').IsEquivalence := sorry

/-- In a 2-commutative triangle of thickenings of algebraic stacks with
cartesian vertical squares, suppose the ambient target is locally of finite
type over the ambient base and the ambient source is flat and locally of
finite presentation over that base. Then the closed-fiber morphism is
an open immersion if and only if the ambient morphism is an open immersion. -/
theorem openImmersion_iff :
    Groupoids.Hom.OpenImmersion f ↔ Groupoids.Hom.OpenImmersion f' := sorry

/-- In a 2-commutative triangle of thickenings of algebraic stacks with
cartesian vertical squares, suppose the ambient target is locally of finite
type over the ambient base and the ambient source is flat and locally of
finite presentation over that base. Then the closed-fiber morphism is
a monomorphism if and only if the ambient morphism is a monomorphism. -/
theorem mono_iff : Groupoids.Hom.Mono f ↔ Groupoids.Hom.Mono f' := sorry

/-- In a 2-commutative triangle of thickenings of algebraic stacks with
cartesian vertical squares, suppose the ambient target is locally of finite
type over the ambient base and the ambient source is flat and locally of
finite presentation over that base. Then the closed-fiber morphism is
locally quasi-finite if and only if the ambient morphism is locally quasi-finite. -/
theorem locallyQuasiFinite_iff :
    LocallyQuasiFinite f ↔ LocallyQuasiFinite f' := sorry

/-- In a 2-commutative triangle of thickenings of algebraic stacks with
cartesian vertical squares, suppose the ambient target is locally of finite
type over the ambient base and the ambient source is flat and locally of
finite presentation over that base. Then the closed-fiber morphism is
syntomic if and only if the ambient morphism is syntomic. -/
theorem syntomic_iff : Syntomic f ↔ Syntomic f' := sorry

/-- In a 2-commutative triangle of thickenings of algebraic stacks with
cartesian vertical squares, suppose the ambient target is locally of finite
type over the ambient base and the ambient source is flat and locally of
finite presentation over that base. Then the closed-fiber morphism is
smooth if and only if the ambient morphism is smooth. -/
theorem smooth_iff : Smooth f ↔ Smooth f' := sorry

/-- In a 2-commutative triangle of thickenings of algebraic stacks with
cartesian vertical squares, suppose the ambient target is locally of finite
type over the ambient base and the ambient source is flat and locally of
finite presentation over that base. Then the closed-fiber morphism is
unramified if and only if the ambient morphism is unramified. -/
theorem unramified_iff : Unramified f ↔ Unramified f' := sorry

/-- In a 2-commutative triangle of thickenings of algebraic stacks with
cartesian vertical squares, suppose the ambient target is locally of finite
type over the ambient base and the ambient source is flat and locally of
finite presentation over that base. Then the closed-fiber morphism is
étale if and only if the ambient morphism is étale. -/
theorem etale_iff : Etale f ↔ Etale f' := sorry

/-- In a 2-commutative triangle of thickenings of algebraic stacks with
cartesian vertical squares, suppose the ambient target is locally of finite
type over the ambient base and the ambient source is flat and locally of
finite presentation over that base. Then the closed-fiber morphism is
finite if and only if the ambient morphism is finite. -/
theorem isFinite_iff : IsFinite f ↔ IsFinite f' := sorry

end AlgebraicGeometry.AlgebraicStack.IsThickening
