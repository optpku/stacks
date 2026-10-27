/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.InternalHom.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Tensor.Canonical
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Canonical derived pullback–Hom comparison -/

@[expose] public section

open CategoryTheory CategoryTheory.DerivedCategory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom

variable {S : Scheme.{u}} {X' X : AlgebraicSpace S}

/-- The canonical derived pullback–Hom map is the transpose of pulled-back evaluation. -/
def canonicalPullbackComparison (g' : X' ⟶ X) (E K : ModuleDerived X) :
    (ModuleDerived.pullback g').obj ((functor E).obj K) ⟶
      (functor ((ModuleDerived.pullback g').obj E)).obj ((ModuleDerived.pullback g').obj K) :=
  (adjunction ((ModuleDerived.pullback g').obj E)).homEquiv _ _
    ((ModuleDerived.pullbackTensorIso g' ((functor E).obj K) E).inv ≫
      (ModuleDerived.pullback g').map ((adjunction E).counit.app K))

/-- Uncurrying the canonical pullback–Hom comparison recovers pulled-back evaluation after
the inverse canonical tensor comparison. -/
theorem canonicalPullbackComparison_spec (g' : X' ⟶ X) (E K : ModuleDerived X) :
    ((adjunction ((ModuleDerived.pullback g').obj E)).homEquiv _ _).symm
        (canonicalPullbackComparison g' E K) =
      (ModuleDerived.pullbackTensorIso g' ((functor E).obj K) E).inv ≫
        (ModuleDerived.pullback g').map ((adjunction E).counit.app K) :=
  Equiv.symm_apply_apply _ _

/-- Relative derived sheaf Hom is naturally pushforward of sheaf Hom after pullback
of its first argument. -/
def canonicalAdjunctionComparisonNatIso (g' : X' ⟶ X) (M : ModuleDerived X) :
    Modules.moduleDerivedPushforward g' ⋙ functor M ≅
      functor ((ModuleDerived.pullback g').obj M) ⋙ Modules.moduleDerivedPushforward g' :=
  (((adjunction M).comp (AlgebraicSpace.derivedPullbackPushforwardAdjunction g')).ofNatIsoLeft
      (ModuleDerived.pullbackTensorNatIso g' M)).rightAdjointUniq
    ((AlgebraicSpace.derivedPullbackPushforwardAdjunction g').comp
      (adjunction ((ModuleDerived.pullback g').obj M)))

/-- The relative derived sheaf Hom identification evaluated at a derived module. -/
def canonicalAdjunctionComparisonIso (g' : X' ⟶ X)
    (M : ModuleDerived X) (L : ModuleDerived X') :
    (functor M).obj ((Modules.moduleDerivedPushforward g').obj L) ≅
      (Modules.moduleDerivedPushforward g').obj
        ((functor ((ModuleDerived.pullback g').obj M)).obj L) :=
  (canonicalAdjunctionComparisonNatIso g' M).app L

/-- Transposing relative derived sheaf Hom gives pullback comparison followed by
sheaf Hom applied to the geometric counit. -/
theorem canonicalAdjunctionComparison_transpose (g' : X' ⟶ X)
    (M : ModuleDerived X) (L : ModuleDerived X') :
    ((AlgebraicSpace.derivedPullbackPushforwardAdjunction g').homEquiv _ _).symm
        (canonicalAdjunctionComparisonIso g' M L).hom =
      canonicalPullbackComparison g' M ((Modules.moduleDerivedPushforward g').obj L) ≫
        (functor ((ModuleDerived.pullback g').obj M)).map
          ((AlgebraicSpace.derivedPullbackPushforwardAdjunction g').counit.app L) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom
