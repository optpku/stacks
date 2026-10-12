/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension
public import ReasLib.Algebra.Homology.CochainComplex.Nat.Derived.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Ext.TStructure

@[expose] public section

/-!
# Cohomology comparisons for derived pullback

This module provides comparisons between derived pullback and ordinary pullback on cohomology,
including their upper- and lower-cohomology-edge forms.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology

/-- The canonical comparison from derived pullback of a single sheaf in degree `i` to the
ordinary pullback placed in the same degree. -/
noncomputable def singlePullbackComparison {X Y : RingedSpace.{u}} (g : X ⟶ Y)
    (M : Y.Modules) (i : ℤ) :
    (RingedSpace.modulePullbackDerived g).obj
        ((DerivedCategory.singleFunctor Y.Modules i).obj M) ⟶
      (DerivedCategory.singleFunctor X.Modules i).obj
        ((RingedSpace.Hom.pullback g).obj M) :=
  let SM := (CochainComplex.singleFunctor Y.Modules i).obj M
  (RingedSpace.modulePullbackDerived g).map
      ((DerivedCategory.singleFunctorIsoCompQ Y.Modules i).hom.app M) ≫
    (RingedSpace.modulePullbackDerived g).map
      ((DerivedCategory.quotientCompQhIso Y.Modules).inv.app SM) ≫
    ((RingedSpace.modulePullbackToDerived g).totalLeftDerivedCounit
      DerivedCategory.Qh (RingedSpace.ModuleQis Y)).app
        ((HomotopyCategory.quotient Y.Modules (up ℤ)).obj SM) ≫
    (Functor.Homotopy.singleIso (RingedSpace.Hom.pullback g) i).hom.app M

/-- On degree-`i` homology, derived pullback of a single sheaf canonically recovers ordinary
pullback. -/
noncomputable def singlePullbackHomologyComparison {X Y : RingedSpace.{u}}
    (g : X ⟶ Y) (M : Y.Modules) (i : ℤ) :
    (DerivedCategory.homologyFunctor X.Modules i).obj
        ((RingedSpace.modulePullbackDerived g).obj
          ((DerivedCategory.singleFunctor Y.Modules i).obj M)) ⟶
      (RingedSpace.Hom.pullback g).obj M :=
  (DerivedCategory.homologyFunctor X.Modules i).map
      (singlePullbackComparison g M i) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules i).hom.app
      ((RingedSpace.Hom.pullback g).obj M)

/-- The single-sheaf homology comparison is obtained by applying homology to
`singlePullbackComparison` and then removing the single-complex realization. -/
theorem singlePullbackHomologyComparison_def {X Y : RingedSpace.{u}}
    (g : X ⟶ Y) (M : Y.Modules) (i : ℤ) :
    singlePullbackHomologyComparison g M i =
      (DerivedCategory.homologyFunctor X.Modules i).map
          (singlePullbackComparison g M i) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules i).hom.app
          ((RingedSpace.Hom.pullback g).obj M) := sorry

/-- The single-sheaf pullback homology comparison is invertible. -/
noncomputable instance singlePullbackHomologyComparison_isIso {X Y : RingedSpace.{u}}
    (g : X ⟶ Y) (M : Y.Modules) (i : ℤ) :
    IsIso (singlePullbackHomologyComparison g M i) := sorry

/-- A derived module bounded above by `i` maps canonically to its degree-`i` cohomology sheaf
placed in degree `i`. -/
noncomputable def upperCohomologyProjection {X : RingedSpace.{u}}
    (E : RingedSpace.ModuleDerived X) (i : ℤ) (hE : E.IsLE i) :
    E ⟶ (DerivedCategory.singleFunctor X.Modules i).obj
      ((DerivedCategory.homologyFunctor X.Modules i).obj E) :=
  (CategoryTheory.ShiftedHom.homEquiv (X := E)
      (Y := (DerivedCategory.singleFunctor X.Modules i).obj
        ((DerivedCategory.homologyFunctor X.Modules i).obj E))
      (i - i) (sub_self i)).symm
    ((DerivedCategory.ShiftedHom.Boundary.toHomologyEquiv E
      ((DerivedCategory.singleFunctor X.Modules i).obj
        ((DerivedCategory.homologyFunctor X.Modules i).obj E)) i i hE inferInstance).symm
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules i).inv.app
        ((DerivedCategory.homologyFunctor X.Modules i).obj E)))

/-- At the upper cohomological edge, derived pullback of the canonical projection induces an
isomorphism on degree-`i` homology. -/
noncomputable instance upperCohomologyProjection_pullback_isIso {X Y : RingedSpace.{u}}
    (g : X ⟶ Y) (E : RingedSpace.ModuleDerived Y) (i : ℤ) (hE : E.IsLE i) :
    IsIso ((DerivedCategory.homologyFunctor X.Modules i).map
      ((RingedSpace.modulePullbackDerived g).map
        (upperCohomologyProjection E i hE))) := sorry

/-- The canonical upper-edge comparison from ordinary pullback of degree-`i` cohomology to
degree-`i` cohomology after derived pullback. -/
noncomputable def upperPullbackComparison {X Y : RingedSpace.{u}}
    (g : X ⟶ Y) (E : RingedSpace.ModuleDerived Y) (i : ℤ) (hE : E.IsLE i)
    [IsIso (singlePullbackHomologyComparison g
      ((DerivedCategory.homologyFunctor Y.Modules i).obj E) i)]
    [IsIso ((DerivedCategory.homologyFunctor X.Modules i).map
      ((RingedSpace.modulePullbackDerived g).map
        (upperCohomologyProjection E i hE)))] :
    (RingedSpace.Hom.pullback g).obj
        ((DerivedCategory.homologyFunctor Y.Modules i).obj E) ⟶
      (DerivedCategory.homologyFunctor X.Modules i).obj
        ((RingedSpace.modulePullbackDerived g).obj E) :=
  inv (singlePullbackHomologyComparison g
      ((DerivedCategory.homologyFunctor Y.Modules i).obj E) i) ≫
    inv ((DerivedCategory.homologyFunctor X.Modules i).map
      ((RingedSpace.modulePullbackDerived g).map
        (upperCohomologyProjection E i hE)))

/-- The upper-edge pullback comparison is the inverse single-sheaf comparison followed by the
inverse of the pulled-back upper cohomology projection. -/
theorem upperPullbackComparison_def {X Y : RingedSpace.{u}}
    (g : X ⟶ Y) (E : RingedSpace.ModuleDerived Y) (i : ℤ) (hE : E.IsLE i)
    [IsIso (singlePullbackHomologyComparison g
      ((DerivedCategory.homologyFunctor Y.Modules i).obj E) i)]
    [IsIso ((DerivedCategory.homologyFunctor X.Modules i).map
      ((RingedSpace.modulePullbackDerived g).map
        (upperCohomologyProjection E i hE)))] :
    upperPullbackComparison g E i hE =
      inv (singlePullbackHomologyComparison g
        ((DerivedCategory.homologyFunctor Y.Modules i).obj E) i) ≫
      inv ((DerivedCategory.homologyFunctor X.Modules i).map
        ((RingedSpace.modulePullbackDerived g).map
          (upperCohomologyProjection E i hE))) := sorry

/-- A lower Tor-amplitude bound supplies the corresponding lower cohomological bound. -/
theorem isGE_of_hasTorAmplitudeGE {X : RingedSpace.{u}}
    {E : RingedSpace.ModuleDerived X} {a : ℤ}
    (hE : RingedSpace.HasTorAmplitudeGE E a) : E.IsGE a := sorry

/-- Derived pullback preserves the lower cohomological bound supplied by lower
Tor-amplitude. -/
theorem pullback_isGE_of_hasTorAmplitudeGE {X Y : RingedSpace.{u}} (g : X ⟶ Y)
    (E : RingedSpace.ModuleDerived Y) (a : ℤ)
    (hE : RingedSpace.HasTorAmplitudeGE E a) :
    ((RingedSpace.modulePullbackDerived g).obj E).IsGE a := sorry

/-- The lowest potentially nonzero cohomology sheaf of a bounded-below derived module maps
canonically into that derived module. -/
noncomputable def lowerCohomologyInclusion {X : RingedSpace.{u}}
    (E : RingedSpace.ModuleDerived X) (a : ℤ) (hE : E.IsGE a) :
    (DerivedCategory.singleFunctor X.Modules a).obj
        (RingedSpace.ModuleDerived.cohomologySheaf E a) ⟶ E :=
  (CategoryTheory.ShiftedHom.homEquiv (X :=
      (DerivedCategory.singleFunctor X.Modules a).obj
        (RingedSpace.ModuleDerived.cohomologySheaf E a))
      (Y := E) (a - a) (sub_self a)).symm
    ((DerivedCategory.ShiftedHom.Boundary.toHomologyEquiv
      ((DerivedCategory.singleFunctor X.Modules a).obj
        (RingedSpace.ModuleDerived.cohomologySheaf E a))
      E a a inferInstance hE).symm
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules a).hom.app
          (RingedSpace.ModuleDerived.cohomologySheaf E a)))

/-- The canonical lower-edge comparison maps ordinary pullback of degree-`a` cohomology to
degree-`a` cohomology after derived pullback. -/
noncomputable def lowerPullbackComparison {X Y : RingedSpace.{u}} (g : X ⟶ Y)
    (E : RingedSpace.ModuleDerived Y) (a : ℤ) (hE : E.IsGE a)
    (hSingle : IsIso (singlePullbackHomologyComparison g
      (RingedSpace.ModuleDerived.cohomologySheaf E a) a)) :
    (RingedSpace.Hom.pullback g).obj
        (RingedSpace.ModuleDerived.cohomologySheaf E a) ⟶
      RingedSpace.ModuleDerived.cohomologySheaf
        ((RingedSpace.modulePullbackDerived g).obj E) a :=
  @inv _ _ _ _ (singlePullbackHomologyComparison g
      (RingedSpace.ModuleDerived.cohomologySheaf E a) a) hSingle ≫
    (DerivedCategory.homologyFunctor X.Modules a).map
      ((RingedSpace.modulePullbackDerived g).map (lowerCohomologyInclusion E a hE))

/-- At the lower endpoint of the Tor-amplitude, the canonical pullback comparison is
invertible. -/
theorem lowerPullbackComparison_isIso {X Y : RingedSpace.{u}} (g : X ⟶ Y)
    (E : RingedSpace.ModuleDerived Y) (a : ℤ)
    (hTor : RingedSpace.HasTorAmplitudeGE E a) (hE : E.IsGE a)
    (hSingle : IsIso (singlePullbackHomologyComparison g
      (RingedSpace.ModuleDerived.cohomologySheaf E a) a)) :
    IsIso (lowerPullbackComparison g E a hE hSingle) := sorry

/-- The lower-edge pullback comparison is natural in the derived module. -/
theorem lowerPullbackComparison_naturality {X Y : RingedSpace.{u}} (g : X ⟶ Y)
    {E F : RingedSpace.ModuleDerived Y} (a : ℤ) (hE : E.IsGE a) (hF : F.IsGE a)
    (hSingleE : IsIso (singlePullbackHomologyComparison g
      (RingedSpace.ModuleDerived.cohomologySheaf E a) a))
    (hSingleF : IsIso (singlePullbackHomologyComparison g
      (RingedSpace.ModuleDerived.cohomologySheaf F a) a))
    (α : E ⟶ F) :
    (RingedSpace.Hom.pullback g).map
          (RingedSpace.ModuleDerived.cohomologySheafMap α a) ≫
        lowerPullbackComparison g F a hF hSingleF =
      lowerPullbackComparison g E a hE hSingleE ≫
        RingedSpace.ModuleDerived.cohomologySheafMap
          ((RingedSpace.modulePullbackDerived g).map α) a := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology
