module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Coherator
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pushforward
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived

/-!
# Derived Functors for Quasicoherent Modules

This module defines the unbounded right-derived coherator and quasicoherent pushforward using
K-injective resolutions, together with their canonical comparison units and universal-property
instances.
-/

@[expose] public section

open CategoryTheory
open ComplexShape
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh.Derived

/-- Quasicoherent modules use their standard derived category. -/
instance hasDerivedCategory (X : Scheme.{u}) : HasDerivedCategory (QCoh X) :=
  HasDerivedCategory.standard (QCoh X)

/-- The K-injective right-derived coherator from derived module sheaves to derived
quasicoherent modules. -/
noncomputable abbrev coherator (X : Scheme.{u}) :
    DerivedCategory X.Modules ⥤ DerivedCategory (QCoh X) :=
  -- Local instance justification (defeq pin): specialize to the canonical sheaf-module instance.
  letI : IsGrothendieckAbelian.{u} X.Modules :=
    inferInstanceAs (IsGrothendieckAbelian.{u} (SheafOfModules.{u} X.ringCatSheaf))
  Functor.RightDerived.KInjective.functor.{u} (QCoh.coherator X)

/-- The cochain-level comparison unit for the right-derived coherator. -/
noncomputable abbrev coheratorUnit (X : Scheme.{u}) :
    (QCoh.coherator X).mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex (QCoh X) ℤ ⥤ DerivedCategory (QCoh X)) ⟶
      (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ DerivedCategory X.Modules) ⋙
        coherator X :=
  -- Local instance justification (defeq pin): specialize to the canonical sheaf-module instance.
  letI : IsGrothendieckAbelian.{u} X.Modules :=
    inferInstanceAs (IsGrothendieckAbelian.{u} (SheafOfModules.{u} X.ringCatSheaf))
  Functor.RightDerived.KInjective.unit.{u} (QCoh.coherator X)

/-- The derived coherator satisfies the universal property of a right-derived functor. -/
instance coheratorIsRightDerived (X : Scheme.{u}) :
    (coherator X).IsRightDerivedFunctor (coheratorUnit X)
      (HomologicalComplex.quasiIso X.Modules (up ℤ)) :=
  -- Local instance justification (defeq pin): specialize to the canonical sheaf-module instance.
  letI : IsGrothendieckAbelian.{u} X.Modules :=
    inferInstanceAs (IsGrothendieckAbelian.{u} (SheafOfModules.{u} X.ringCatSheaf))
  Functor.RightDerived.KInjective.isRightDerived (QCoh.coherator X)

/-- The K-injective right-derived pushforward on quasicoherent modules along a quasi-compact,
quasi-separated morphism. -/
noncomputable abbrev pushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    DerivedCategory (QCoh X) ⥤ DerivedCategory (QCoh Y) :=
  -- Local instance justification (search instability): pin the K-injective universe for `QCoh X`.
  letI : IsGrothendieckAbelian.{u} (QCoh X) :=
    QCoh.instIsGrothendieckAbelian X
  Functor.RightDerived.KInjective.functor.{u} (QCoh.pushforward f)

/-- The cochain-level comparison unit for right-derived quasicoherent pushforward. -/
noncomputable abbrev pushforwardUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    (QCoh.pushforward f).mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex (QCoh Y) ℤ ⥤ DerivedCategory (QCoh Y)) ⟶
      (DerivedCategory.Q : CochainComplex (QCoh X) ℤ ⥤ DerivedCategory (QCoh X)) ⋙
        pushforward f :=
  -- Local instance justification (search instability): pin the K-injective universe for `QCoh X`.
  letI : IsGrothendieckAbelian.{u} (QCoh X) :=
    QCoh.instIsGrothendieckAbelian X
  Functor.RightDerived.KInjective.unit.{u} (QCoh.pushforward f)

/-- Derived quasicoherent pushforward satisfies the universal property of a right-derived
functor. -/
instance pushforwardIsRightDerived {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    (pushforward f).IsRightDerivedFunctor (pushforwardUnit f)
      (HomologicalComplex.quasiIso (QCoh X) (up ℤ)) :=
  -- Local instance justification (search instability): pin the K-injective universe for `QCoh X`.
  letI : IsGrothendieckAbelian.{u} (QCoh X) :=
    QCoh.instIsGrothendieckAbelian X
  Functor.RightDerived.KInjective.isRightDerived (QCoh.pushforward f)

end AlgebraicGeometry.Scheme.QCoh.Derived
