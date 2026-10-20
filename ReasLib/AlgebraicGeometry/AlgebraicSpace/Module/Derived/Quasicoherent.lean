/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Coherator
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Comparison

/-! # Derived coherator and quasi-coherent pushforward on algebraic spaces

K-injective total right-derived functors of the coherator and of quasi-coherent
pushforward, with their canonical cochain comparisons and universal properties.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

/-- Quasi-coherent pushforward along a qcqs morphism of algebraic spaces is additive. -/
instance pushforward.additive {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    (pushforward f).Additive :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.QCoh

namespace AlgebraicGeometry.AlgebraicSpace.QCoh.Derived

/-- The K-injective right-derived coherator from derived module sheaves to derived
quasi-coherent modules on an algebraic space. -/
noncomputable abbrev coherator {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ModuleDerived X ⥤ DerivedCategory (QCoh X) :=
  Functor.RightDerived.KInjective.functor.{u} (QCoh.coherator X)

/-- The cochain-level comparison unit for the right-derived coherator. -/
noncomputable abbrev coheratorUnit {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (QCoh.coherator X).mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex (QCoh X) ℤ ⥤ DerivedCategory (QCoh X)) ⟶
      (DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ DerivedCategory (Modules X)) ⋙
        coherator X :=
  Functor.RightDerived.KInjective.unit.{u} (QCoh.coherator X)

/-- The derived coherator satisfies the universal property of a right-derived functor. -/
instance coheratorIsRightDerived {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (coherator X).IsRightDerivedFunctor (coheratorUnit X)
      (HomologicalComplex.quasiIso (Modules X) (up ℤ)) :=
  Functor.RightDerived.KInjective.isRightDerived (QCoh.coherator X)

/-- The K-injective right-derived pushforward on quasi-coherent modules along a
quasi-compact, quasi-separated morphism of algebraic spaces. -/
noncomputable abbrev pushforward {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    DerivedCategory (QCoh X) ⥤ DerivedCategory (QCoh Y) :=
  -- The auxiliary derived-functor instance has an undetermined Grothendieck-size
  -- universe; select its original-universe specialization explicitly.
  @Functor.RightDerived.KInjective.functor.{u} _ _ _ _ _ _ _ _
    (QCoh.pushforward f) _ _
    (Functor.RightDerived.KInjective.hasDerived.{u} (QCoh.pushforward f))

/-- The cochain-level comparison unit for right-derived quasi-coherent pushforward. -/
noncomputable abbrev pushforwardUnit {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    (QCoh.pushforward f).mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex (QCoh Y) ℤ ⥤ DerivedCategory (QCoh Y)) ⟶
      (DerivedCategory.Q : CochainComplex (QCoh X) ℤ ⥤ DerivedCategory (QCoh X)) ⋙
        pushforward f :=
  @Functor.RightDerived.KInjective.unit.{u} _ _ _ _ _ _ _ _
    (QCoh.pushforward f) _ _
    (Functor.RightDerived.KInjective.hasDerived.{u} (QCoh.pushforward f))

/-- Derived quasi-coherent pushforward satisfies the universal property of a
right-derived functor. -/
instance pushforwardIsRightDerived {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    (pushforward f).IsRightDerivedFunctor (pushforwardUnit f)
      (HomologicalComplex.quasiIso (QCoh X) (up ℤ)) :=
  @Functor.RightDerived.KInjective.isRightDerived.{u} _ _ _ _ _ _ _ _
    (QCoh.pushforward f) _ _
    (Functor.RightDerived.KInjective.hasDerived.{u} (QCoh.pushforward f))

end AlgebraicGeometry.AlgebraicSpace.QCoh.Derived
