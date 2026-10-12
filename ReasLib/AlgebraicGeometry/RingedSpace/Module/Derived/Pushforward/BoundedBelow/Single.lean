/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.SingleFunctor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.BoundedBelow
public import ReasLib.CategoryTheory.DerivedCategory.Bounded.SingleFunctor.Localization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-below derived pushforward of a single object

This file specializes the generic map from a bounded-below cochain map into a right-derived value
to direct image of module sheaves.  The public comparison is expressed with the canonical
single-object functors in `D⁺`; cochain and homotopy localization models remain internal bridges.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.moduleDerivedPushforwardPlus

variable {X Y : RingedSpace.{u}}

/-- The bounded-below cochain map from `G[0]` to the termwise pushforward of `F[0]` induced by an
`f`-map `G ⟶ f_* F`. -/
@[stacks 01F9 "bounded cochain map of an f-map"]
noncomputable def cochainComparison (f : X ⟶ Y) {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) :
    (CochainComplex.Plus.singleFunctor Y.Modules 0).obj G ⟶
      (RingedSpace.Hom.pushforward f).mapCochainComplexPlus.obj
        ((CochainComplex.Plus.singleFunctor X.Modules 0).obj F) :=
  (CochainComplex.Plus.ι Y.Modules).preimage
    ((CochainComplex.Plus.singleFunctorCompιIso Y.Modules 0).hom.app G ≫
      (CochainComplex.singleFunctor Y.Modules 0).map φ ≫
      ((RingedSpace.Hom.pushforward f).mapCochainComplexSingleFunctor 0).inv.app F ≫
      ((RingedSpace.Hom.pushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((CochainComplex.Plus.singleFunctorCompιIso X.Modules 0).inv.app F) ≫
      ((RingedSpace.Hom.pushforward f).mapCochainComplexPlusCompι).inv.app
        ((CochainComplex.Plus.singleFunctor X.Modules 0).obj F))

/-- A map `G ⟶ f_* F` induces the canonical bounded-below morphism
`G[0] ⟶ Rf_*(F[0])`. -/
@[stacks 01F9 "bounded derived-pushforward map of an f-map"]
noncomputable def comparison (f : X ⟶ Y) {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) :
    (DerivedCategory.Plus.singleFunctor Y.Modules 0).obj G ⟶
      (moduleDerivedPushforwardPlus f).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj F) :=
  (DerivedCategory.Plus.singleFunctor.fromHomotopy.iso Y.Modules 0).inv.app G ≫
    DerivedCategory.Plus.Qh.map
      ((CochainComplex.Plus.singleFunctorCompQuotientIso Y.Modules 0).inv.app G) ≫
    Functor.RightDerived.Bounded.fromCochainMap
      (RingedSpace.Hom.pushforward f) (cochainComparison f φ) ≫
    (moduleDerivedPushforwardPlus f).map
      (DerivedCategory.Plus.Qh.map
          ((CochainComplex.Plus.singleFunctorCompQuotientIso X.Modules 0).hom.app F) ≫
        (DerivedCategory.Plus.singleFunctor.fromHomotopy.iso X.Modules 0).hom.app F)

/-- The bounded direct-image comparison is the generic `fromCochainMap` construction transported
across the standard single-object localization isomorphisms. -/
@[stacks 01F9 "bounded derived-pushforward comparison formula"]
theorem comparison_eq (f : X ⟶ Y) {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) :
    comparison f φ =
      (DerivedCategory.Plus.singleFunctor.fromHomotopy.iso Y.Modules 0).inv.app G ≫
        DerivedCategory.Plus.Qh.map
          ((CochainComplex.Plus.singleFunctorCompQuotientIso Y.Modules 0).inv.app G) ≫
        Functor.RightDerived.Bounded.fromCochainMap
          (RingedSpace.Hom.pushforward f) (cochainComparison f φ) ≫
        (moduleDerivedPushforwardPlus f).map
          (DerivedCategory.Plus.Qh.map
              ((CochainComplex.Plus.singleFunctorCompQuotientIso
                X.Modules 0).hom.app F) ≫
            (DerivedCategory.Plus.singleFunctor.fromHomotopy.iso
              X.Modules 0).hom.app F) := sorry

end AlgebraicGeometry.RingedSpace.moduleDerivedPushforwardPlus
