module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Height
import StacksCheckRecall

/-!
# Heights associated to invertible modules on projective varieties

The three height conclusions are stated in the associated-height library.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Height Scheme.Modules
open scoped AlgebraicGeometry CategoryTheory.MonObj

noncomputable section

universe u

/- Exercise 111.65.4 (Heights) (1) -/
@[stacks 0GYC] #check (AlgebraicGeometry.Height.compAutomorphismSubPullbackBddAbove :
  ∀ {K : Type u} [Field K]
    (X : SchemeOverField K) [ProjectiveVariety X]
    (hP : (n : ℕ) → (SchemeOverField.point K ⟶ ProjectiveSpace.schemeOver K n) → ℝ)
    (h : (L : X.left.Modules) → Invertible L →
      (SchemeOverField.point K ⟶ X) → ℝ)
    (h_eq : ProjectiveCompatible X hP h)
    (h_tensor : TensorCompatible X h) (h_iso : IsoCompatible X h)
    (L : X.left.Modules) [hL : Invertible L] (α : X ⟶ X) [IsIso α],
    BddAbove (Set.range fun P : SchemeOverField.point K ⟶ X ↦
      |h L hL (P ≫ α) -
        h ((pullback α.left).obj L) inferInstance P|))

/- Exercise 111.65.4 (Heights) (2) -/
@[stacks 0GYC] #check (AlgebraicGeometry.Height.tensorPullbackInverseUnbounded :
  ∀ {K : Type u}
    [Field K] (X : SchemeOverField K) [ProjectiveVariety X]
    (hP : (n : ℕ) → (SchemeOverField.point K ⟶ ProjectiveSpace.schemeOver K n) → ℝ)
    (h : (L : X.left.Modules) → Invertible L →
      (SchemeOverField.point K ⟶ X) → ℝ)
    (h_eq : ProjectiveCompatible X hP h)
    (h_tensor : TensorCompatible X h) (h_iso : IsoCompatible X h)
    (L : X.left.Modules) [hL : Invertible L] (α : X ⟶ X) [IsIso α]
    (h_unbounded :
      ¬ BddAbove (Set.range fun P : SchemeOverField.point K ⟶ X ↦
          |h L hL P - h L hL (P ≫ α)|)),
    ¬ BddAbove (Set.range fun P : SchemeOverField.point K ⟶ X ↦
        |h (L ⊗ isInvertibleObject.inverse
            ((pullback α.left).obj L))
          inferInstance P|))

/- Exercise 111.65.4 (Heights) (3) -/
@[stacks 0GYC] #check (AlgebraicGeometry.Height.existsDegreeZeroUnbounded :
  ∀ {K : Type u} [Field K]
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
      ¬ BddAbove (Set.range fun P : SchemeOverField.point K ⟶ X ↦ |h L hL P|)),
    ∃ (N : X.left.Modules) (hN : Invertible N),
      hN.curveDegree X.hom hdim.le = 0 ∧
        ¬ BddAbove (Set.range fun P : SchemeOverField.point K ⟶ X ↦ |h N hN P|))
