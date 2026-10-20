/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.TotalComposition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.TorIndependence
public import ReasLib.CategoryTheory.Adjunction.BaseChange

/-! # Tor-independent derived base change on algebraic spaces

A commutative square of algebraic spaces induces the unbounded derived mate
`Lg^* Rf_* ⟶ Rf'_* L(g')^*`. For a Tor-independent cartesian square with
quasi-compact and quasi-separated vertical morphism, this map is invertible on
every derived module with quasi-coherent cohomology.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.DerivedBaseChange

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}

/-- The source functor `Rf_* ⋙ Lg^*` of unbounded derived base change. -/
abbrev source (f : X ⟶ Y) (g : Y' ⟶ Y) :
    ModuleDerived X ⥤ ModuleDerived Y' :=
  Modules.moduleDerivedPushforward f ⋙
    Functor.LeftDerived.Homotopy.functor (Modules.pullback g)

/-- The target functor `L(g')^* ⋙ Rf'_*` of unbounded derived base change. -/
abbrev target (g' : X' ⟶ X) (f' : X' ⟶ Y') :
    ModuleDerived X ⥤ ModuleDerived Y' :=
  Functor.LeftDerived.Homotopy.functor (Modules.pullback g') ⋙
    Modules.moduleDerivedPushforward f'

variable {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- A commutative square of algebraic spaces canonically identifies the two
composites of total derived module pullbacks. -/
def pullbackCartesianIso (sq : CommSq g' f' f g) :
    Functor.LeftDerived.Homotopy.functor (Modules.pullback g) ⋙
        Functor.LeftDerived.Homotopy.functor (Modules.pullback f') ≅
      Functor.LeftDerived.Homotopy.functor (Modules.pullback f) ⋙
        Functor.LeftDerived.Homotopy.functor (Modules.pullback g') :=
  asIso (ModuleDerived.totalPullbackCompComparison f' g) ≪≫
    eqToIso (congrArg (fun h : X' ⟶ Y ↦
      Functor.LeftDerived.Homotopy.functor (Modules.pullback h)) sq.w.symm) ≪≫
    (asIso (ModuleDerived.totalPullbackCompComparison g' f)).symm

/-- The derived square identification composes the forward composition
comparison, the square equality, and the inverse composition comparison. -/
theorem pullbackCartesianIso_hom (sq : CommSq g' f' f g) :
    (pullbackCartesianIso sq).hom =
      ModuleDerived.totalPullbackCompComparison f' g ≫
        eqToHom (congrArg (fun h : X' ⟶ Y ↦
          Functor.LeftDerived.Homotopy.functor (Modules.pullback h)) sq.w.symm) ≫
          inv (ModuleDerived.totalPullbackCompComparison g' f) := by
  simp only [pullbackCartesianIso, Iso.trans_hom, asIso_hom, Iso.symm_hom,
    asIso_inv, eqToIso.hom]

/-- The canonical unbounded derived base-change transformation associated to a
commutative square of algebraic spaces. -/
def map (sq : CommSq g' f' f g) : source f g ⟶ target g' f' :=
  CategoryTheory.DerivedBaseChange.map
    (Modules.derivedPullbackPushforwardAdjunction f)
    (Modules.derivedPullbackPushforwardAdjunction f')
    (pullbackCartesianIso sq)

/-- The component of the unbounded derived base-change transformation at a
derived module. -/
abbrev app (sq : CommSq g' f' f g) (E : ModuleDerived X) :
    (source f g).obj E ⟶ (target g' f').obj E :=
  (map sq).app E

/-- Transposing the canonical derived base-change component recovers the square
comparison followed by the derived pullback of the counit. -/
theorem map_spec (sq : CommSq g' f' f g) (E : ModuleDerived X) :
    ((Modules.derivedPullbackPushforwardAdjunction f').homEquiv
        ((source f g).obj E)
        ((Functor.LeftDerived.Homotopy.functor (Modules.pullback g')).obj E)).symm
        (app sq E) =
      (pullbackCartesianIso sq).hom.app ((Modules.moduleDerivedPushforward f).obj E) ≫
        (Functor.LeftDerived.Homotopy.functor (Modules.pullback g')).map
          ((Modules.derivedPullbackPushforwardAdjunction f).counit.app E) :=
  CategoryTheory.DerivedBaseChange.map_spec
    (Modules.derivedPullbackPushforwardAdjunction f)
    (Modules.derivedPullbackPushforwardAdjunction f') (pullbackCartesianIso sq) E

end AlgebraicGeometry.AlgebraicSpace.Hom.DerivedBaseChange

namespace AlgebraicGeometry.AlgebraicSpace.TorIndependentBaseChange

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}

/-- For a Tor-independent cartesian square whose vertical map is quasi-compact
and quasi-separated, every component of the canonical unbounded derived
base-change transformation on a derived module with quasi-coherent cohomology
is invertible. -/
theorem map_app_isIso (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (sq : IsPullback g' f' f g)
    (hTor : TorIndependentOver (Over.mk f) (Over.mk g))
    (E : DerivedQCoh X) :
    IsIso ((Hom.DerivedBaseChange.map sq.toCommSq).app E.obj) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.TorIndependentBaseChange
