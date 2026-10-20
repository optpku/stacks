/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Real.Basic
public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Over
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist.Invertible
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Symmetric
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Point
public import ReasLib.CategoryTheory.Monoidal.Invertible

/-!
# Associated heights of invertible modules

Associated heights compatible with projective-space pullbacks, tensor products, and module
isomorphisms are functorial modulo bounded functions under automorphisms. These compatibility
properties describe the constructed associated heights rather than axioms for projective heights.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open Scheme.Modules
open scoped AlgebraicGeometry CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.Height

/-- Associated heights of pullbacks of the twisting sheaf `𝒪(1)` agree with the given
projective-space heights. -/
def ProjectiveCompatible {K : Type u} [Field K] (X : SchemeOverField K)
    (hP : (n : ℕ) → (SchemeOverField.point K ⟶ ProjectiveSpace.schemeOver K n) → ℝ)
    (h : (L : X.left.Modules) → Invertible L →
      (SchemeOverField.point K ⟶ X) → ℝ) : Prop :=
  ∀ (n : ℕ) (φ : X ⟶ ProjectiveSpace.schemeOver K n)
    (P : SchemeOverField.point K ⟶ X),
    h ((pullback φ.left).obj (ProjectiveSpace.twistingSheaf K n (1 : ℤ)))
      (Invertible.pullback φ.left
        (ProjectiveSpace.twistingSheaf.instInvertible K n (1 : ℤ))) P =
      hP n (P ≫ φ)

/-- Projective compatibility is pointwise equality with the projective height on every
pullback of the twisting sheaf `𝒪(1)`. -/
theorem projectiveCompatible_iff {K : Type u} [Field K]
    (X : SchemeOverField K)
    (hP : (n : ℕ) → (SchemeOverField.point K ⟶ ProjectiveSpace.schemeOver K n) → ℝ)
    (h : (L : X.left.Modules) → Invertible L →
      (SchemeOverField.point K ⟶ X) → ℝ) :
    ProjectiveCompatible X hP h ↔
      ∀ (n : ℕ) (φ : X ⟶ ProjectiveSpace.schemeOver K n)
        (P : SchemeOverField.point K ⟶ X),
        h ((pullback φ.left).obj
            (ProjectiveSpace.twistingSheaf K n (1 : ℤ)))
          (Invertible.pullback φ.left
            (ProjectiveSpace.twistingSheaf.instInvertible K n (1 : ℤ))) P =
          hP n (P ≫ φ) := sorry

/-- Tensor products of invertible modules are additive for associated heights up to a
bounded amount. -/
def TensorCompatible {K : Type u} [Field K] (X : SchemeOverField K)
    (h : (L : X.left.Modules) → Invertible L →
      (SchemeOverField.point K ⟶ X) → ℝ) : Prop :=
  ∀ (L M : X.left.Modules) [hL : Invertible L]
    [hM : Invertible M],
    BddAbove (Set.range fun P : SchemeOverField.point K ⟶ X ↦
      |h (L ⊗ M) inferInstance P - h L hL P - h M hM P|)

/-- Tensor compatibility is boundedness of the absolute error in tensor additivity. -/
theorem tensorCompatible_iff {K : Type u} [Field K] (X : SchemeOverField K)
    (h : (L : X.left.Modules) → Invertible L →
      (SchemeOverField.point K ⟶ X) → ℝ) :
    TensorCompatible X h ↔
      ∀ (L M : X.left.Modules) [hL : Invertible L]
        [hM : Invertible M],
        BddAbove (Set.range fun P : SchemeOverField.point K ⟶ X ↦
          |h (L ⊗ M) inferInstance P - h L hL P - h M hM P|) := sorry

/-- Associated heights of isomorphic invertible modules differ by a bounded amount. -/
def IsoCompatible {K : Type u} [Field K] (X : SchemeOverField K)
    (h : (L : X.left.Modules) → Invertible L →
      (SchemeOverField.point K ⟶ X) → ℝ) : Prop :=
  ∀ (L M : X.left.Modules) (hL : Invertible L)
    (hM : Invertible M),
    Nonempty (L ≅ M) →
      BddAbove (Set.range fun P : SchemeOverField.point K ⟶ X ↦
        |h L hL P - h M hM P|)

/-- Isomorphism compatibility is boundedness of the absolute height difference for
isomorphic invertible modules. -/
theorem isoCompatible_iff {K : Type u} [Field K] (X : SchemeOverField K)
    (h : (L : X.left.Modules) → Invertible L →
      (SchemeOverField.point K ⟶ X) → ℝ) :
    IsoCompatible X h ↔
      ∀ (L M : X.left.Modules) (hL : Invertible L)
        (hM : Invertible M),
        Nonempty (L ≅ M) →
          BddAbove (Set.range fun P : SchemeOverField.point K ⟶ X ↦
            |h L hL P - h M hM P|) := sorry

/-- Composing an associated height with an automorphism of a projective variety differs
from the height of the pullback module by a bounded amount. -/
theorem compAutomorphismSubPullbackBddAbove {K : Type u} [Field K]
    (X : SchemeOverField K) [ProjectiveVariety X]
    (hP : (n : ℕ) → (SchemeOverField.point K ⟶ ProjectiveSpace.schemeOver K n) → ℝ)
    (h : (L : X.left.Modules) → Invertible L →
      (SchemeOverField.point K ⟶ X) → ℝ)
    (h_eq : ProjectiveCompatible X hP h)
    (h_tensor : TensorCompatible X h) (h_iso : IsoCompatible X h)
    (L : X.left.Modules) [hL : Invertible L] (α : X ⟶ X) [IsIso α] :
    BddAbove (Set.range fun P : SchemeOverField.point K ⟶ X ↦
      |h L hL (P ≫ α) -
        h ((pullback α.left).obj L) inferInstance P|) := sorry

/-- An unbounded difference between an associated height and its composition with an
automorphism yields an unbounded height for the tensor product with the inverse pullback. -/
theorem tensorPullbackInverseUnbounded {K : Type u}
    [Field K] (X : SchemeOverField K) [ProjectiveVariety X]
    (hP : (n : ℕ) → (SchemeOverField.point K ⟶ ProjectiveSpace.schemeOver K n) → ℝ)
    (h : (L : X.left.Modules) → Invertible L →
      (SchemeOverField.point K ⟶ X) → ℝ)
    (h_eq : ProjectiveCompatible X hP h)
    (h_tensor : TensorCompatible X h) (h_iso : IsoCompatible X h)
    (L : X.left.Modules) [hL : Invertible L] (α : X ⟶ X) [IsIso α]
    (h_unbounded :
      ¬ BddAbove (Set.range fun P : SchemeOverField.point K ⟶ X ↦
          |h L hL P - h L hL (P ≫ α)|)) :
    ¬ BddAbove (Set.range fun P : SchemeOverField.point K ⟶ X ↦
        |h (L ⊗ isInvertibleObject.inverse
            ((pullback α.left).obj L))
          inferInstance P|) := sorry

/-- On a one-dimensional abelian variety, an unbounded height of a symmetric ample
invertible module yields an invertible module of degree zero with unbounded height. -/
theorem existsDegreeZeroUnbounded {K : Type u} [Field K]
    (X : SchemeOverField K) [ProjectiveVariety X] [GrpObj X] [AbelianVariety X]
    (hdim : topologicalKrullDim X.left = 1)
    (hP : (n : ℕ) → (SchemeOverField.point K ⟶ ProjectiveSpace.schemeOver K n) → ℝ)
    (h : (L : X.left.Modules) → Invertible L →
      (SchemeOverField.point K ⟶ X) → ℝ)
    (h_eq : ProjectiveCompatible X hP h)
    (h_tensor : TensorCompatible X h) (h_iso : IsoCompatible X h)
    (L : X.left.Modules) [hL : Invertible L]
    [IsAmple L] (h_sym : IsSymmetric X L)
    (h_unbounded :
      ¬ BddAbove (Set.range fun P : SchemeOverField.point K ⟶ X ↦ |h L hL P|)) :
    ∃ (N : X.left.Modules) (hN : Invertible N),
      hN.curveDegree X.hom hdim.le = 0 ∧
        ¬ BddAbove (Set.range fun P : SchemeOverField.point K ⟶ X ↦ |h N hN P|) := sorry

end AlgebraicGeometry.Height
