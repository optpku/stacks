/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Lemma_66_29_7_Quasicoherent
public import stacks_project.Chap66.Proposition_66_32_2_Coherator
public import stacks_project.Chap67.Lemma_67_11_2_Pushforward
public import stacks_project.Chap75.«75_5_1_1_Comparison»
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh

/-!
# Derived coherator and quasicoherent pushforward on algebraic spaces

K-injective total right-derived functors of the underived coherator and of
qcqs quasicoherent pushforward, together with Grothendieck and additivity
instances needed to form them.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Sheaves of modules on the small étale site of an algebraic space form a Grothendieck
abelian category. -/
instance instIsGrothendieckAbelian {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsGrothendieckAbelian.{u} (Modules X) :=
  sorry

/-- Module pushforward along a morphism of algebraic spaces is additive. -/
instance pushforward.additive {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (pushforward f).Additive :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

/-- Quasi-coherent modules on an algebraic space are Grothendieck abelian in universe `u`. -/
instance instIsGrothendieckAbelianU {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsGrothendieckAbelian.{u} (QCoh X) :=
  instIsGrothendieckAbelian X

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
  Functor.RightDerived.KInjective.functor.{u} (QCoh.pushforward f)

/-- The cochain-level comparison unit for right-derived quasi-coherent pushforward. -/
noncomputable abbrev pushforwardUnit {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    (QCoh.pushforward f).mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex (QCoh Y) ℤ ⥤ DerivedCategory (QCoh Y)) ⟶
      (DerivedCategory.Q : CochainComplex (QCoh X) ℤ ⥤ DerivedCategory (QCoh X)) ⋙
        pushforward f :=
  Functor.RightDerived.KInjective.unit.{u} (QCoh.pushforward f)

/-- Derived quasi-coherent pushforward satisfies the universal property of a
right-derived functor. -/
instance pushforwardIsRightDerived {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    (pushforward f).IsRightDerivedFunctor (pushforwardUnit f)
      (HomologicalComplex.quasiIso (QCoh X) (up ℤ)) :=
  Functor.RightDerived.KInjective.isRightDerived (QCoh.pushforward f)

end AlgebraicGeometry.AlgebraicSpace.QCoh.Derived
