/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Pullback
public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Homology
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

/-! # Cohomology and arbitrary derived pullback

The comparison in degree `n` uses the upper edge of `τ≤n E` and the actual
truncation inclusion `τ≤n E ⟶ E`. It requires neither a bound on `E` nor flatness
of the morphism. Its upper-bounded specialization is the existing edge map.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology

/-- The single-module derived-pullback counit, assembled as a natural
transformation from the same single-complex comparison used objectwise. -/
def singlePullbackComparisonNatTrans {X Y : RingedSpace.{u}} (g : X ⟶ Y) (n : ℤ) :
    DerivedCategory.singleFunctor Y.Modules n ⋙ modulePullbackDerived g ⟶
      RingedSpace.Hom.pullback g ⋙ DerivedCategory.singleFunctor X.Modules n :=
  (Functor.isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQ Y.Modules n)
      (modulePullbackDerived g)).hom ≫
    (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (CochainComplex.singleFunctor Y.Modules n)
        (DerivedCategory.quotientCompQhIso Y.Modules)).symm (modulePullbackDerived g)).hom ≫
    Functor.whiskerLeft
      (CochainComplex.singleFunctor Y.Modules n ⋙ HomotopyCategory.quotient Y.Modules
        (ComplexShape.up ℤ))
      ((modulePullbackToDerived g).totalLeftDerivedCounit
        DerivedCategory.Qh (RingedSpace.ModuleQis Y)) ≫
    (Functor.Homotopy.singleIso (RingedSpace.Hom.pullback g) n).hom

/-- The natural single comparison has precisely the existing objectwise counit as
its component. -/
@[simp]
theorem singlePullbackComparisonNatTrans_app {X Y : RingedSpace.{u}} (g : X ⟶ Y)
    (M : Y.Modules) (n : ℤ) :
    (singlePullbackComparisonNatTrans g n).app M = singlePullbackComparison g M n := rfl

/-- Naturality of the upper cohomology projection obtained from the boundary equivalence. -/
theorem upperCohomologyProjection_naturality {X : RingedSpace.{u}}
    {E F : DerivedCategory X.Modules} (a : E ⟶ F) (n : ℤ)
    (hE : E.IsLE n) (hF : F.IsLE n) :
    a ≫ upperCohomologyProjection F n hF =
      upperCohomologyProjection E n hE ≫
        (DerivedCategory.singleFunctor X.Modules n).map
          ((DerivedCategory.homologyFunctor X.Modules n).map a) := by
  unfold upperCohomologyProjection
  simp only [ShiftedHom.homEquiv, Equiv.coe_fn_symm_mk]
  rw (config := { transparency := .all }) [← Category.assoc,
    ← DerivedCategory.ShiftedHom.Boundary.toHomologyEquiv_naturality_left_symm
      n n hE hF inferInstance a]
  rw (config := { transparency := .all }) [(DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules n).inv.naturality]
  rw (config := { transparency := .all }) [DerivedCategory.ShiftedHom.Boundary.toHomologyEquiv_naturality_right_symm
    n n hE inferInstance inferInstance]
  simp only [Category.assoc]
  rw (config := { transparency := .all }) [(shiftFunctorZero' (DerivedCategory X.Modules) (n - n) (sub_self n)).hom.naturality]
  rfl


/-- The natural homology comparison for a single module after derived pullback. -/
def singlePullbackHomologyNatTrans {X Y : RingedSpace.{u}} (g : X ⟶ Y) (n : ℤ) :
    DerivedCategory.singleFunctor Y.Modules n ⋙ modulePullbackDerived g ⋙
        DerivedCategory.homologyFunctor X.Modules n ⟶ RingedSpace.Hom.pullback g :=
  Functor.whiskerRight (singlePullbackComparisonNatTrans g n)
      (DerivedCategory.homologyFunctor X.Modules n) ≫
    (Functor.isoWhiskerLeft (RingedSpace.Hom.pullback g)
      (DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules n)).hom

/-- The natural comparison computes to the original homology-level single counit. -/
@[simp]
theorem singlePullbackHomologyNatTrans_app {X Y : RingedSpace.{u}} (g : X ⟶ Y)
    (M : Y.Modules) (n : ℤ) :
    (singlePullbackHomologyNatTrans g n).app M = singlePullbackHomologyComparison g M n := rfl

/-- Upper truncation at `n` preserves degree-`n` cohomology. -/
instance truncationHomology_isIso {X : RingedSpace.{u}}
    (E : DerivedCategory X.Modules) (n : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor X.Modules n).map
      ((DerivedCategory.TStructure.t.truncLEι n).app E)) :=
  CategoryTheory.DerivedCategory.TruncLT.homologyMap_isIso E (n + 1) n (by omega)

/-- The natural cohomology isomorphism induced by the upper-truncation inclusion. -/
def truncationHomologyNatIso (X : RingedSpace.{u}) (n : ℤ) :
    DerivedCategory.TStructure.t.truncLE n ⋙ DerivedCategory.homologyFunctor X.Modules n ≅
      DerivedCategory.homologyFunctor X.Modules n :=
  NatIso.ofComponents
    (fun E => @asIso _ _ _ _ ((DerivedCategory.homologyFunctor X.Modules n).map
      ((DerivedCategory.TStructure.t.truncLEι n).app E))
      (truncationHomology_isIso (X := X) E n))
    (fun a => (Functor.whiskerRight (DerivedCategory.TStructure.t.truncLEι n)
      (DerivedCategory.homologyFunctor X.Modules n)).naturality a)

/-- The upper-edge comparison is natural between objects bounded above by the same
degree. It compares the existing projection and single-sheaf counit constructions. -/
@[reassoc]
theorem upperPullbackComparison_naturality {X Y : RingedSpace.{u}} (g : X ⟶ Y)
    {E F : DerivedCategory Y.Modules} (a : E ⟶ F) (n : ℤ)
    (hE : E.IsLE n) (hF : F.IsLE n) :
    (RingedSpace.Hom.pullback g).map ((DerivedCategory.homologyFunctor Y.Modules n).map a) ≫
        upperPullbackComparison g F n hF =
      upperPullbackComparison g E n hE ≫
        (DerivedCategory.homologyFunctor X.Modules n).map ((modulePullbackDerived g).map a) := by
  let eE :=
    (@asIso _ _ _ _ ((DerivedCategory.homologyFunctor X.Modules n).map
      ((modulePullbackDerived g).map (upperCohomologyProjection E n hE)))
      (upperCohomologyProjection_pullback_isIso g E n hE)) ≪≫
    (@asIso _ _ _ _ (singlePullbackHomologyComparison g
      ((DerivedCategory.homologyFunctor Y.Modules n).obj E) n)
      (singlePullbackHomologyComparison_isIso g _ n))
  let eF :=
    (@asIso _ _ _ _ ((DerivedCategory.homologyFunctor X.Modules n).map
      ((modulePullbackDerived g).map (upperCohomologyProjection F n hF)))
      (upperCohomologyProjection_pullback_isIso g F n hF)) ≪≫
    (@asIso _ _ _ _ (singlePullbackHomologyComparison g
      ((DerivedCategory.homologyFunctor Y.Modules n).obj F) n)
      (singlePullbackHomologyComparison_isIso g _ n))
  have hp := congrArg ((modulePullbackDerived g ⋙ DerivedCategory.homologyFunctor X.Modules n).map)
    (upperCohomologyProjection_naturality a n hE hF)
  simp only [Functor.map_comp, Functor.comp_map] at hp
  have hs := (singlePullbackHomologyNatTrans g n).naturality
    ((DerivedCategory.homologyFunctor Y.Modules n).map a)
  change (DerivedCategory.homologyFunctor X.Modules n).map
      ((modulePullbackDerived g).map ((DerivedCategory.singleFunctor Y.Modules n).map
        ((DerivedCategory.homologyFunctor Y.Modules n).map a))) ≫
      singlePullbackHomologyComparison g ((DerivedCategory.homologyFunctor Y.Modules n).obj F) n =
    singlePullbackHomologyComparison g ((DerivedCategory.homologyFunctor Y.Modules n).obj E) n ≫
      (RingedSpace.Hom.pullback g).map ((DerivedCategory.homologyFunctor Y.Modules n).map a) at hs
  have hn : (DerivedCategory.homologyFunctor X.Modules n).map
      ((modulePullbackDerived g).map a) ≫ eF.hom =
      eE.hom ≫ (RingedSpace.Hom.pullback g).map
        ((DerivedCategory.homologyFunctor Y.Modules n).map a) := by
    simp only [eE, eF, Iso.trans_hom, asIso_hom]
    rw (config := { transparency := .all }) [← Category.assoc, hp, Category.assoc, hs, Category.assoc]
    simp only [singlePullbackHomologyComparison, Category.assoc]
  change (RingedSpace.Hom.pullback g).map
      ((DerivedCategory.homologyFunctor Y.Modules n).map a) ≫ eF.inv =
    eE.inv ≫ (DerivedCategory.homologyFunctor X.Modules n).map ((modulePullbackDerived g).map a)
  apply (cancel_epi eE.hom).mp
  apply (cancel_mono eF.hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Iso.hom_inv_id_assoc, Category.comp_id] using hn.symm

/-- The upper-edge comparison on the functorial upper truncation. -/
def truncatedUpperPullbackNatTrans {X Y : RingedSpace.{u}} (g : X ⟶ Y) (n : ℤ) :
    DerivedCategory.TStructure.t.truncLE n ⋙
        DerivedCategory.homologyFunctor Y.Modules n ⋙ RingedSpace.Hom.pullback g ⟶
      DerivedCategory.TStructure.t.truncLE n ⋙
        modulePullbackDerived g ⋙ DerivedCategory.homologyFunctor X.Modules n where
  app E := upperPullbackComparison g ((DerivedCategory.TStructure.t.truncLE n).obj E) n
    inferInstance
  naturality {_ _} a := upperPullbackComparison_naturality g
    ((DerivedCategory.TStructure.t.truncLE n).map a) n inferInstance inferInstance

/-- The canonical natural comparison from ordinary pullback of cohomology to
cohomology of derived pullback, in every integer degree. -/
def pullbackComparisonNatTrans {X Y : RingedSpace.{u}} (g : X ⟶ Y) (n : ℤ) :
    DerivedCategory.homologyFunctor Y.Modules n ⋙ RingedSpace.Hom.pullback g ⟶
      modulePullbackDerived g ⋙ DerivedCategory.homologyFunctor X.Modules n :=
  (Functor.isoWhiskerRight (truncationHomologyNatIso Y n).symm
    (RingedSpace.Hom.pullback g)).hom ≫
    truncatedUpperPullbackNatTrans g n ≫
    Functor.whiskerRight (DerivedCategory.TStructure.t.truncLEι n)
      (modulePullbackDerived g ⋙ DerivedCategory.homologyFunctor X.Modules n)

/-- The objectwise canonical comparison for arbitrary derived modules. -/
def pullbackComparison {X Y : RingedSpace.{u}} (g : X ⟶ Y)
    (E : DerivedCategory Y.Modules) (n : ℤ) :
    (RingedSpace.Hom.pullback g).obj ((DerivedCategory.homologyFunctor Y.Modules n).obj E) ⟶
      (DerivedCategory.homologyFunctor X.Modules n).obj ((modulePullbackDerived g).obj E) :=
  (pullbackComparisonNatTrans g n).app E

/-- Naturality follows from the natural transformations in the construction. -/
@[reassoc]
theorem pullbackComparison_naturality {X Y : RingedSpace.{u}} (g : X ⟶ Y)
    {E F : DerivedCategory Y.Modules} (a : E ⟶ F) (n : ℤ) :
    (RingedSpace.Hom.pullback g).map ((DerivedCategory.homologyFunctor Y.Modules n).map a) ≫
        pullbackComparison g F n =
      pullbackComparison g E n ≫
        (DerivedCategory.homologyFunctor X.Modules n).map ((modulePullbackDerived g).map a) :=
  (pullbackComparisonNatTrans g n).naturality a

/-- Multiplying by the actual truncation comparison recovers the upper-edge
comparison followed by derived pullback of the truncation inclusion. -/
@[reassoc]
theorem truncationHomology_comp_pullbackComparison {X Y : RingedSpace.{u}}
    (g : X ⟶ Y) (E : DerivedCategory Y.Modules) (n : ℤ) :
    (RingedSpace.Hom.pullback g).map
        ((DerivedCategory.homologyFunctor Y.Modules n).map
          ((DerivedCategory.TStructure.t.truncLEι n).app E)) ≫
        pullbackComparison g E n =
      upperPullbackComparison g ((DerivedCategory.TStructure.t.truncLE n).obj E) n
          inferInstance ≫
        (DerivedCategory.homologyFunctor X.Modules n).map
          ((modulePullbackDerived g).map ((DerivedCategory.TStructure.t.truncLEι n).app E)) := by
  change ((RingedSpace.Hom.pullback g).mapIso ((truncationHomologyNatIso Y n).app E)).hom ≫
    ((RingedSpace.Hom.pullback g).mapIso ((truncationHomologyNatIso Y n).app E)).inv ≫ _ = _
  exact Iso.hom_inv_id_assoc _ _

/-- On an object bounded above by `n`, the general comparison is exactly the
existing upper-edge comparison, not an independently chosen isomorphism. -/
theorem pullbackComparison_eq_upper {X Y : RingedSpace.{u}} (g : X ⟶ Y)
    (E : DerivedCategory Y.Modules) (n : ℤ) (hE : E.IsLE n) :
    pullbackComparison g E n = upperPullbackComparison g E n hE := by
  apply (cancel_epi ((RingedSpace.Hom.pullback g).map
    ((DerivedCategory.homologyFunctor Y.Modules n).map
      ((DerivedCategory.TStructure.t.truncLEι n).app E)))).mp
  rw [truncationHomology_comp_pullbackComparison]
  exact (upperPullbackComparison_naturality g
    ((DerivedCategory.TStructure.t.truncLEι n).app E) n inferInstance hE).symm

/-- The canonical comparison is invertible at the highest potentially nonzero
cohomological degree, for arbitrary base change. -/
theorem pullbackComparison_isIso_of_isLE {X Y : RingedSpace.{u}} (g : X ⟶ Y)
    (E : DerivedCategory Y.Modules) (n : ℤ) (hE : E.IsLE n) :
    IsIso (pullbackComparison g E n) := by
  rw [pullbackComparison_eq_upper g E n hE]
  unfold upperPullbackComparison
  infer_instance

end AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology
