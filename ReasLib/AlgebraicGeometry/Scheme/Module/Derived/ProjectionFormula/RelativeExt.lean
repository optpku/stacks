/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Triangulated
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ProjectionFormula.Ext

@[expose] public section

/-!
# Relative Ext delta functors

This module packages the relative Ext functor associated to a scheme morphism and two
derived modules, together with the predicate that a derived module on the base represents it.
-/

open AlgebraicGeometry CategoryTheory
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open RingedSpace.Module.Derived RingedSpace.ModuleDerived

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.ProjectionFormula

/-- The delta functor in the quasicoherent coefficient variable with value
`F ↦ RΓ(X, RHom(K, E ⊗ Lf^*(F[0])))`. -/
noncomputable def relativeExtDelta {X S : Scheme.{u}} (f : X ⟶ S)
    (K E : RingedSpace.ModuleDerived X.toRingedSpace)
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)] :
    DeltaFunctor S.Modules (DerivedCategory AddCommGrpCat.{u}) :=
  let P := RingedSpace.modulePullbackDerived f.toShHom
  let T := @MonoidalCategory.tensorLeft _ _
    (RingedSpace.ModuleDerived.monoidalCategory X.toRingedSpace) E
  let H := (ihom K : RingedSpace.ModuleDerived X.toRingedSpace ⥤
    RingedSpace.ModuleDerived X.toRingedSpace)
  let hPComm : P.CommShift ℤ :=
    RingedSpace.modulePullbackDerived.commShift f.toShHom
  let hPTri : P.IsTriangulatedWith hPComm :=
    RingedSpace.modulePullbackDerived.isTriangulated f.toShHom
  let Dpull := @DeltaFunctor.postcomposeExactFunctor
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (GlobalSections.Delta.single S.toRingedSpace) P hPComm hPTri
  let Dtensor := Dpull.postcomposeExactFunctor T
  let Dhom := Dtensor.postcomposeExactFunctor H
  let Dsections := Dhom.postcomposeExactFunctor
    (RingedSpace.moduleDerivedGlobalSections X.toRingedSpace)
  Dsections.postcomposeExactFunctor
    (forget₂ (ModuleCat X.toRingedSpace.globalSectionsRing)
      AddCommGrpCat.{u}).mapDerivedCategory

/-- Evaluation of `relativeExtDelta` is derived global sections of the internal Hom from
`K` to `E` tensored with the derived pullback of the coefficient in degree zero. -/
theorem relativeExtDelta_obj {X S : Scheme.{u}} (f : X ⟶ S)
    (K E : RingedSpace.ModuleDerived X.toRingedSpace)
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    (F : S.Modules) :
    (relativeExtDelta f K E).obj F =
      (GlobalSections.toAbelian X.toRingedSpace).obj
        ((ihom K).obj
          (E ⊗ (RingedSpace.modulePullbackDerived f.toShHom).obj
            ((DerivedCategory.singleFunctor S.Modules 0).obj F))) := sorry

/-- A complex `L` represents the relative Ext functor when its Ext functor admits a
boundary-compatible natural comparison to `relativeExtDelta` that is invertible in every
integer degree. -/
def RepresentsRelativeExt {X S : Scheme.{u}} (f : X ⟶ S)
    (K E : RingedSpace.ModuleDerived X.toRingedSpace)
    (L : RingedSpace.ModuleDerived S.toRingedSpace)
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    [KFlat.HomotopyTensorDescends S.toRingedSpace]
    [KFlat.TensorDescends S.toRingedSpace]
    [KFlat.IsLocalization S.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)] : Prop :=
  ∃ α : CohomologyTransform (representedExtDelta S L) (relativeExtDelta f K E),
    ∀ i : ℤ, IsIso (α.app i)

/-- The defining criterion for `RepresentsRelativeExt`: a boundary-compatible comparison
whose degreewise natural transformations are all isomorphisms. -/
theorem representsRelativeExt_iff {X S : Scheme.{u}} (f : X ⟶ S)
    (K E : RingedSpace.ModuleDerived X.toRingedSpace)
    (L : RingedSpace.ModuleDerived S.toRingedSpace)
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    [KFlat.HomotopyTensorDescends S.toRingedSpace]
    [KFlat.TensorDescends S.toRingedSpace]
    [KFlat.IsLocalization S.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)] :
    RepresentsRelativeExt f K E L ↔
      ∃ α : CohomologyTransform (representedExtDelta S L) (relativeExtDelta f K E),
        ∀ i : ℤ, IsIso (α.app i) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.ProjectionFormula
