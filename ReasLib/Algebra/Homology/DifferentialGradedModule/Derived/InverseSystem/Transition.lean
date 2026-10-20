/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Restriction.Derived.Sequential
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.InverseSystem.Localization
public import ReasLib.Algebra.Homology.DifferentialGradedModule.InverseSystem.Transition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Transition maps between derived evaluations of module systems

Every transition of an ordinary DG-module system descends through the global localization
`D(ℕ, A)`.  Restriction of scalars gives its linear form, and the extension-restriction
adjunction gives the canonical extension comparison used by quasi-coherent systems.
-/

@[expose] public section

noncomputable section

universe u x v

open CategoryTheory Opposite

namespace DifferentialGradedModule.InverseSystem.Derived

variable {R : Type u} [CommRing R]

namespace Restriction

/-- The component before global localization of the restriction-form transition from stage
`j` to stage `i`. -/
def sourceApp
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    {i j : ℕ} (hij : i ≤ j) (M : System.{u, x, v} A) :
    (stageSource A j).obj M ⟶
      ((stageSource A i ⋙ CochainDGAlgebra.Hom.Derived.restriction
        (A.transitionMap hij)).obj M) :=
  (DifferentialGradedModule.Derived.Q (A.obj (op j))).map
      ((DifferentialGradedModule.toK (A.obj (op j))).map (M.mapLE hij)) ≫
    (CochainDGAlgebra.Hom.Derived.restrictionFac
      (A.transitionMap hij)).inv.app
        ((DifferentialGradedModule.toK (A.obj (op i))).obj (M.obj i))

/-- Before global localization, arbitrary transitions give a natural comparison to restriction
of scalars. -/
@[stacks 0GZI "restriction-form transition before global localization"]
def source
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    {i j : ℕ} (hij : i ≤ j) :
    stageSource.{u, x, v} A j ⟶
      stageSource A i ⋙ CochainDGAlgebra.Hom.Derived.restriction
        (A.transitionMap hij) where
  app M := sourceApp A hij M
  naturality := sorry

/-- The restriction-form transition between derived stage evaluations on `D(ℕ, A)`. -/
@[stacks 0GZI "restriction-form transition on the global derived category"]
noncomputable def comparison
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    {i j : ℕ} (hij : i ≤ j) :
    eval.{u, x, v} A j ⟶
      eval A i ⋙ CochainDGAlgebra.Hom.Derived.restriction
        (A.transitionMap hij) :=
  Localization.liftNatTrans
    (Q A) (quasiIso A)
    (stageSource A j)
    (stageSource A i ⋙ CochainDGAlgebra.Hom.Derived.restriction
      (A.transitionMap hij))
    (eval A j)
    (eval A i ⋙ CochainDGAlgebra.Hom.Derived.restriction
      (A.transitionMap hij))
    (source A hij)

/-- On a represented system, the descended restriction-form transition is the source
transition conjugated by the canonical factorization isomorphisms. -/
theorem comparison_app_Q
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    {i j : ℕ} (hij : i ≤ j) (M : System.{u, x, v} A) :
    (comparison A hij).app ((Q A).obj M) =
      (evalFactors A j).hom.app M ≫
        (source A hij).app M ≫
          (Functor.isoWhiskerRight (evalFactors A i)
            (CochainDGAlgebra.Hom.Derived.restriction
              (A.transitionMap hij))).inv.app M := sorry

/-- The restriction-form transition over a reflexive inequality is the canonical identity
comparison. -/
@[simp]
theorem comparison_refl
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) (i : ℕ) :
    comparison.{u, x, v} A (le_refl i) =
      Functor.whiskerLeft (eval A i)
        (CochainDGAlgebra.InverseSystem.Derived.restrictionReflIso A i).hom := sorry

/-- Restriction-form transitions compose through every intermediate index. -/
theorem comparison_comp
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    comparison.{u, x, v} A (Nat.le_trans hij hjk) =
      comparison A hjk ≫
        Functor.whiskerRight (comparison A hij)
          (CochainDGAlgebra.Hom.Derived.restriction (A.transitionMap hjk)) ≫
        Functor.whiskerLeft (eval A i)
          (CochainDGAlgebra.InverseSystem.Derived.restrictionCompIso
            A hij hjk).hom := sorry

end Restriction

namespace Left

/-- Derived restriction along the opposite of a transition in a sequential DGA system. -/
@[stacks 0GZI "derived restriction along a left DGA-system transition"]
noncomputable abbrev restriction
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    {i j : ℕ} (hij : i ≤ j) :
    DifferentialGradedModule.Derived.Category.{u, v}
          (A.obj (op i)).opposite ⥤
      DifferentialGradedModule.Derived.Category.{u, v}
        (A.obj (op j)).opposite :=
  CochainDGAlgebra.Hom.Derived.restriction
    (A.transitionMap hij).opposite

/-- Restriction along a reflexive transition of the opposite DGA tower is canonically the
identity functor. -/
noncomputable abbrev restrictionReflIso
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) (i : ℕ) :
    𝟭 (DifferentialGradedModule.Derived.Category.{u, v}
        (A.obj (op i)).opposite) ≅
      restriction A (le_refl i) :=
  CochainDGAlgebra.InverseSystem.Derived.restrictionReflIso
    (A ⋙ CochainDGAlgebra.oppositeFunctor R) i

/-- Successive restrictions along opposite DGA transitions are canonically identified with
restriction along the composite transition. -/
noncomputable abbrev restrictionCompIso
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    restriction A hij ⋙ restriction A hjk ≅
      restriction A (Nat.le_trans hij hjk) :=
  CochainDGAlgebra.InverseSystem.Derived.restrictionCompIso
    (A ⋙ CochainDGAlgebra.oppositeFunctor R) hij hjk

/-- The restriction-form transition between derived evaluations of global left DG-module
systems. -/
@[stacks 0GZI "restriction-form transition for global left derived systems"]
noncomputable abbrev comparison
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    {i j : ℕ} (hij : i ≤ j) :
    eval.{u, x, v} A j ⟶ eval A i ⋙ restriction A hij :=
  Restriction.comparison
    (A ⋙ CochainDGAlgebra.oppositeFunctor R) hij

/-- The restriction-form transition of a global left derived system over a reflexive inequality
is the canonical identity comparison. -/
@[simp]
theorem comparison_refl
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) (i : ℕ) :
    comparison.{u, x, v} A (le_refl i) =
      Functor.whiskerLeft (eval A i) (restrictionReflIso A i).hom := sorry

/-- Restriction-form transitions of global left derived systems compose through every
intermediate index. -/
theorem comparison_comp
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    comparison.{u, x, v} A (Nat.le_trans hij hjk) =
      comparison A hjk ≫
        Functor.whiskerRight (comparison A hij) (restriction A hjk) ≫
        Functor.whiskerLeft (eval A i) (restrictionCompIso A hij hjk).hom := sorry

end Left

/-- Before global localization, the transition from stage `j` to stage `i` in extension form is
the adjoint of its restriction-form comparison. -/
@[stacks 0GZI "extension transition before global localization"]
noncomputable def comparisonSourceLE
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    {i j : ℕ} (hij : i ≤ j) :
    stageSource.{u, x, x} A j ⋙
        CochainDGAlgebra.Hom.Derived.extension (A.transitionMap hij) ⟶
      stageSource A i where
  app M :=
    (CochainDGAlgebra.Hom.Derived.homEquiv
      (A.transitionMap hij) ((stageSource A j).obj M)
        ((stageSource A i).obj M)).symm
      ((Restriction.source A hij).app M)
  naturality := sorry

/-- Evaluation of the source extension comparison is the adjoint of the restriction-form
transition. -/
theorem comparisonSourceLE_app
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    {i j : ℕ} (hij : i ≤ j) (M : System.{u, x, x} A) :
    (comparisonSourceLE A hij).app M =
      (CochainDGAlgebra.Hom.Derived.homEquiv
        (A.transitionMap hij) ((stageSource A j).obj M)
          ((stageSource A i).obj M)).symm
        ((Restriction.source A hij).app M) := sorry

/-- The extension-form transition between arbitrary derived stage evaluations on `D(ℕ, A)`. -/
@[stacks 0GZI "extension transition on the global derived category"]
noncomputable def comparisonLE
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    {i j : ℕ} (hij : i ≤ j) :
    eval.{u, x, x} A j ⋙
        CochainDGAlgebra.Hom.Derived.extension (A.transitionMap hij) ⟶
      eval A i :=
  Localization.liftNatTrans
    (Q A) (quasiIso A)
    (stageSource A j ⋙
      CochainDGAlgebra.Hom.Derived.extension (A.transitionMap hij))
    (stageSource A i)
    (eval A j ⋙
      CochainDGAlgebra.Hom.Derived.extension (A.transitionMap hij))
    (eval A i) (comparisonSourceLE A hij)

/-- On a represented system, the descended extension transition is the source comparison
conjugated by the canonical factorization isomorphisms. -/
theorem comparisonLE_app_Q
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    {i j : ℕ} (hij : i ≤ j) (M : System.{u, x, x} A) :
    (comparisonLE A hij).app ((Q A).obj M) =
      (Functor.isoWhiskerRight (evalFactors A j)
          (CochainDGAlgebra.Hom.Derived.extension
            (A.transitionMap hij))).hom.app M ≫
        (comparisonSourceLE A hij).app M ≫
          (evalFactors A i).inv.app M := sorry

/-- The extension transition over a reflexive inequality is the canonical identity
comparison. -/
@[simp]
theorem comparisonLE_refl
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) (i : ℕ) :
    comparisonLE A (le_refl i) =
      Functor.whiskerLeft (eval A i)
        (CochainDGAlgebra.InverseSystem.Derived.extensionReflIso A i).hom := sorry

/-- Extension transitions compose through every intermediate index. -/
theorem comparisonLE_comp
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    comparisonLE A (Nat.le_trans hij hjk) =
      Functor.whiskerLeft (eval A k)
          (CochainDGAlgebra.InverseSystem.Derived.extensionCompIso
            A hij hjk).inv ≫
        Functor.whiskerRight (comparisonLE A hjk)
          (CochainDGAlgebra.Hom.Derived.extension (A.transitionMap hij)) ≫
        comparisonLE A hij := sorry

end DifferentialGradedModule.InverseSystem.Derived
