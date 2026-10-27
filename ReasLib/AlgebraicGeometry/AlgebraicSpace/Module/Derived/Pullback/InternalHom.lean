/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Tensor.Isomorphism
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Closed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Derived pullback and internal Hom -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalClosed
open CategoryTheory.DerivedCategory CategoryTheory.Functor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom

variable {S : Scheme.{u}} {X' X : AlgebraicSpace S}
variable [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
variable [MonoidalCategory (ModuleDerived X')] [BraidedCategory (ModuleDerived X')]

/-- The canonical pullback/internal-Hom map is the transpose of pulled-back evaluation,
using the structure-ring derived tensor and explicit ambient tensor models. -/
def pullbackComparison (g' : X' ⟶ X)
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (T_X : DerivedTensor.Right.Monoidal.Model (C := X.Modules))
    (T_X' : DerivedTensor.Right.Monoidal.Model (C := X'.Modules))
    (M K : ModuleDerived X) :
    (LeftDerived.Homotopy.functor (Modules.pullback g')).obj ((H_X.ihomOf M).obj K) ⟶
      (H_X'.ihomOf ((LeftDerived.Homotopy.functor (Modules.pullback g')).obj M)).obj
        ((LeftDerived.Homotopy.functor (Modules.pullback g')).obj K) :=
  (DerivedTensor.Right.Closed.adjunctionOf H_X' T_X'
    ((LeftDerived.Homotopy.functor (Modules.pullback g')).obj M)).homEquiv _ _
    ((DerivedQCoh.rightTensorComparisonIso g' ((H_X.ihomOf M).obj K) M).inv ≫
      (LeftDerived.Homotopy.functor (Modules.pullback g')).map
        ((DerivedTensor.Right.Closed.adjunctionOf H_X T_X M).counit.app K))

/-- Transposing the pullback/internal-Hom comparison recovers the inverse tensor comparison
followed by pullback of evaluation. -/
theorem pullbackComparison_spec (g' : X' ⟶ X)
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (T_X : DerivedTensor.Right.Monoidal.Model (C := X.Modules))
    (T_X' : DerivedTensor.Right.Monoidal.Model (C := X'.Modules))
    (M K : ModuleDerived X) :
    ((DerivedTensor.Right.Closed.adjunctionOf H_X' T_X'
      ((LeftDerived.Homotopy.functor (Modules.pullback g')).obj M)).homEquiv _ _).symm
        (pullbackComparison g' H_X H_X' T_X T_X' M K) =
      (DerivedQCoh.rightTensorComparisonIso g' ((H_X.ihomOf M).obj K) M).inv ≫
        (LeftDerived.Homotopy.functor (Modules.pullback g')).map
          ((DerivedTensor.Right.Closed.adjunctionOf H_X T_X M).counit.app K) :=
  Equiv.symm_apply_apply _ _


/-- Relative derived internal Hom is identified with pushforward of internal Hom after
pullback of its first argument, by uniqueness of right adjoints to fixed-right tensoring. -/
def adjunctionComparisonIso (g' : X' ⟶ X)
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (T_X : DerivedTensor.Right.Monoidal.Model (C := X.Modules))
    (T_X' : DerivedTensor.Right.Monoidal.Model (C := X'.Modules))
    (M : ModuleDerived X) (L : ModuleDerived X') :
    (H_X.ihomOf M).obj ((Modules.moduleDerivedPushforward g').obj L) ≅
      (Modules.moduleDerivedPushforward g').obj
        ((H_X'.ihomOf ((LeftDerived.Homotopy.functor (Modules.pullback g')).obj M)).obj L) :=
  ((((DerivedTensor.Right.Closed.adjunctionOf H_X T_X M).comp
      (Modules.derivedPullbackPushforwardAdjunction g')).ofNatIsoLeft
        (DerivedQCoh.rightTensorComparisonNatIso g' M)).rightAdjointUniq
    ((Modules.derivedPullbackPushforwardAdjunction g').comp
      (DerivedTensor.Right.Closed.adjunctionOf H_X' T_X'
        ((LeftDerived.Homotopy.functor (Modules.pullback g')).obj M)))).app L

/-- The transpose of the relative internal-Hom identification is the pullback comparison
followed by internal Hom applied to the pullback-pushforward counit. -/
theorem adjunctionComparison_transpose (g' : X' ⟶ X)
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (T_X : DerivedTensor.Right.Monoidal.Model (C := X.Modules))
    (T_X' : DerivedTensor.Right.Monoidal.Model (C := X'.Modules))
    (M : ModuleDerived X) (L : ModuleDerived X') :
    ((Modules.derivedPullbackPushforwardAdjunction g').homEquiv _ _).symm
        (adjunctionComparisonIso g' H_X H_X' T_X T_X' M L).hom =
      pullbackComparison g' H_X H_X' T_X T_X' M
          ((Modules.moduleDerivedPushforward g').obj L) ≫
        (H_X'.ihomOf ((LeftDerived.Homotopy.functor (Modules.pullback g')).obj M)).map
          ((Modules.derivedPullbackPushforwardAdjunction g').counit.app L) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom
