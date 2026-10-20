/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Localization.Predicate
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy
public import ReasLib.Algebra.Homology.DifferentialGradedModule.InverseSystem.QuasiIso
import Mathlib.Tactic.CrossRefAttribute

/-!
# The derived category of differential graded module systems

This file defines `D(ℕ, A)` by localizing the single category of DG-module systems over
`A : SequentialInverseSystem (CochainDGAlgebra R)` at levelwise quasi-isomorphisms.  Stage evaluation descends from
this global localization to the usual derived category of modules over each `A n`.
-/

@[expose] public section

noncomputable section

universe u x v

open CategoryTheory Opposite

namespace DifferentialGradedModule.InverseSystem.Derived

variable {R : Type u} [CommRing R]

/-- The global derived category `D(ℕ, A)` of DG-module systems over `A`. -/
@[stacks 0GZG "derived category of DG-module systems"]
abbrev Category (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) :=
  (quasiIso.{u, x, v} A).Localization

/-- The canonical localization from DG-module systems to `D(ℕ, A)`. -/
@[stacks 0GZG "localization of DG-module systems"]
abbrev Q (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) :
    System.{u, x, v} A ⥤ Category.{u, x, v} A :=
  (quasiIso.{u, x, v} A).Q

/-- Before localization, evaluation at stage `n` lands in the ordinary derived category by first
passing through the DG homotopy category. -/
def stageSource (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) (n : ℕ) :
    System.{u, x, v} A ⥤
      DifferentialGradedModule.Derived.Category.{u, v} (A.obj (op n)) :=
  System.eval A n ⋙ DifferentialGradedModule.toK (A.obj (op n)) ⋙
    DifferentialGradedModule.Derived.Q (A.obj (op n))

/-- Stage evaluation sends every levelwise quasi-isomorphism to an isomorphism. -/
theorem stageSource_inverts
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) (n : ℕ) :
    (quasiIso A).IsInvertedBy (stageSource A n) := sorry

/-- Evaluation at stage `n` on the global derived category `D(ℕ, A)`. -/
@[stacks 0GZG "derived stage evaluation for DG-module systems"]
noncomputable def eval
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) (n : ℕ) :
    Category A ⥤ DifferentialGradedModule.Derived.Category.{u, v} (A.obj (op n)) :=
  CategoryTheory.Localization.Construction.lift
    (stageSource A n) (stageSource_inverts A n)

/-- Derived stage evaluation factors the source evaluation through the global localization. -/
noncomputable def evalFactors
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) (n : ℕ) :
    Q A ⋙ eval A n ≅ stageSource A n :=
  eqToIso (CategoryTheory.Localization.Construction.fac
    (stageSource A n) (stageSource_inverts A n))

/-- Derived stage evaluation is the canonical localization lift of its source-level functor. -/
@[stacks 0GZG "lifting property of derived stage evaluation"]
noncomputable instance evalLifting
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) (n : ℕ) :
    CategoryTheory.Localization.Lifting (Q A) (quasiIso A)
      (stageSource A n) (eval A n) :=
  ⟨evalFactors A n⟩

namespace Left

/-- The global derived category of left DG-module systems over `A`, modeled over the opposite DGA
tower. -/
@[stacks 0GZG "derived category of left DG-module systems"]
abbrev Category (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) :=
  DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v}
    (A ⋙ CochainDGAlgebra.oppositeFunctor R)

/-- The canonical localization from left DG-module systems to their global derived category. -/
@[stacks 0GZG "localization of left DG-module systems"]
abbrev Q (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) :
    DifferentialGradedModule.InverseSystem.LeftSystem.{u, x, v} A ⥤ Category A :=
  DifferentialGradedModule.InverseSystem.Derived.Q
    (A ⋙ CochainDGAlgebra.oppositeFunctor R)

/-- Before localization, left-system evaluation at stage `n` lands in the derived category of
right modules over `(A.obj (op n)).opposite`. -/
abbrev stageSource
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) (n : ℕ) :
    DifferentialGradedModule.InverseSystem.LeftSystem.{u, x, v} A ⥤
      DifferentialGradedModule.Derived.Category.{u, v}
        (A.obj (op n)).opposite :=
  DifferentialGradedModule.InverseSystem.Derived.stageSource
    (A ⋙ CochainDGAlgebra.oppositeFunctor R) n

/-- Derived evaluation of a global left DG-module system at one stage, represented as a right
module over the opposite DGA. -/
@[stacks 0GZI "derived stage evaluation of a left DG-module inverse system"]
abbrev eval
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) (n : ℕ) :
    Category A ⥤ DifferentialGradedModule.Derived.Category.{u, v}
      (A.obj (op n)).opposite :=
  DifferentialGradedModule.InverseSystem.Derived.eval
    (A ⋙ CochainDGAlgebra.oppositeFunctor R) n

/-- Derived left-system evaluation factors its source evaluation through the global
localization. -/
@[stacks 0GZI "factorization of derived left-system evaluation"]
noncomputable abbrev evalFactors
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) (n : ℕ) :
    Q A ⋙ eval A n ≅ stageSource A n :=
  DifferentialGradedModule.InverseSystem.Derived.evalFactors
    (A ⋙ CochainDGAlgebra.oppositeFunctor R) n

/-- The canonical localization lifting data for derived left-system evaluation. The corresponding
instance is already supplied by `DifferentialGradedModule.InverseSystem.Derived.evalLifting`. -/
@[stacks 0GZI "lifting property of derived left-system evaluation"]
noncomputable abbrev evalLifting
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) (n : ℕ) :
    CategoryTheory.Localization.Lifting (Q A)
      (quasiIso (A ⋙ CochainDGAlgebra.oppositeFunctor R))
      (stageSource A n) (eval A n) :=
  DifferentialGradedModule.InverseSystem.Derived.evalLifting
    (A ⋙ CochainDGAlgebra.oppositeFunctor R) n

end Left

/-- Compatibility alias for `Left.Category`. -/
abbrev LeftCategory (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) :=
  Left.Category.{u, x, v} A

/-- Compatibility alias for `Left.eval`. -/
abbrev leftEval
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) (n : ℕ) :
    LeftCategory A ⥤ DifferentialGradedModule.Derived.Category.{u, v}
      (A.obj (op n)).opposite :=
  Left.eval A n

end DifferentialGradedModule.InverseSystem.Derived
