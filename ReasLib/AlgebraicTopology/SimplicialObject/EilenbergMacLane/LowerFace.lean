/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.LowerFace
public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.LowerFace.Signed
public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.Splitting.LowerFace
public import ReasLib.AlgebraicTopology.SimplicialObject.EilenbergMacLane.Functor
public import ReasLib.AlgebraicTopology.SimplicialObject.EilenbergMacLane.Truncation
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 0199

# Lower-face normalized Moore complexes of Eilenberg--MacLane objects

The canonical `eilenbergMacLane` object is the Mathlib `Γ₀` construction. This file exposes its
source-facing lower-face degree comparison using the signed normalized Moore functor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open HomologicalComplex
open scoped Simplicial

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.eilenbergMacLane.normalizedMoore.lowerFace

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The lower-face normalized subobject of the canonical `K(B, k)` is the top subobject in its
distinguished degree.  This is the source-facing term computation; the canonical object itself is
the `Γ₀(single)` construction from `eilenbergMacLane.functor`. -/
@[stacks 0199 "canonical Eilenberg-MacLane lower-face top subobject"]
theorem subobject_eq_top (B : A) (k : ℕ) :
    normalizedMoore.lowerFace.subobject (eilenbergMacLane B k) k = ⊤ := sorry

/-- The lower-face normalized subobject of `K(B, k)` is zero in every degree different from `k`.
This is the subobject-level form of the off-degree vanishing statement and is useful before
passing to the signed chain-complex owner. -/
@[stacks 0199 "canonical Eilenberg-MacLane lower-face off-degree subobject"]
theorem subobject_eq_bot (B : A) (k i : ℕ) (h : i ≠ k) :
    normalizedMoore.lowerFace.subobject (eilenbergMacLane B k) i = ⊥ := sorry

/-- The degree-`k` lower-face normalized term of the canonical `K(B, k)` is explicitly identified
with `B`.  The map is built from the normalized subobject arrow, the truncation comparison, and
the canonical top component of the concentrated object. -/
@[stacks 0199 "canonical Eilenberg-MacLane lower-face degree comparison"]
noncomputable def objIso (B : A) (k : ℕ) :
    ((AlgebraicTopology.normalizedMooreComplex.lowerFace (A := A)).obj
      (eilenbergMacLane B k)).X k ≅ B where
  hom :=
    (normalizedMoore.lowerFace.subobject (eilenbergMacLane B k) k).arrow ≫
      (eilenbergMacLane.degreeIso B k).hom
  inv :=
    (eilenbergMacLane.degreeIso B k).inv ≫
      normalizedMoore.lowerFace.splitting.projection (eilenbergMacLane B k) k
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of the canonical lower-face Eilenberg--MacLane degree comparison. -/
@[simp, stacks 0199 "canonical Eilenberg-MacLane lower-face degree comparison map"]
theorem objIso_hom (B : A) (k : ℕ) :
    (objIso B k).hom =
      (normalizedMoore.lowerFace.subobject (eilenbergMacLane B k) k).arrow ≫
        (eilenbergMacLane.degreeIso B k).hom := sorry

/-- The inverse map of the canonical lower-face Eilenberg--MacLane degree comparison. -/
@[simp, stacks 0199 "canonical Eilenberg-MacLane lower-face degree comparison inverse"]
theorem objIso_inv (B : A) (k : ℕ) :
    (objIso B k).inv =
      (eilenbergMacLane.degreeIso B k).inv ≫
        normalizedMoore.lowerFace.splitting.projection (eilenbergMacLane B k) k := sorry

/-- The canonical lower-face degree comparison is natural in the coefficient object. -/
@[stacks 0199 "canonical Eilenberg-MacLane lower-face degree naturality"]
theorem objIso.hom_naturality (k : ℕ) {B D : A} (f : B ⟶ D) :
    ((eilenbergMacLane.functor k ⋙
        AlgebraicTopology.normalizedMooreComplex.lowerFace).map f).f k ≫
          (objIso D k).hom =
      (objIso B k).hom ≫ f := sorry

/-- The inverse canonical lower-face degree comparison is natural in the coefficient object. -/
@[stacks 0199 "inverse canonical Eilenberg-MacLane lower-face degree naturality"]
theorem objIso.inv_naturality (k : ℕ) {B D : A} (f : B ⟶ D) :
    f ≫ (objIso D k).inv =
      (objIso B k).inv ≫
        ((eilenbergMacLane.functor k ⋙
          AlgebraicTopology.normalizedMooreComplex.lowerFace).map f).f k := sorry

/-- The degree-`k` lower-face normalized term comparison is functorial in coefficients. -/
@[stacks 0199 "canonical Eilenberg-MacLane lower-face degreewise comparison"]
noncomputable def evalIso (k : ℕ) :
    (eilenbergMacLane.functor k ⋙
      AlgebraicTopology.normalizedMooreComplex.lowerFace) ⋙
        HomologicalComplex.eval A (ComplexShape.down ℕ) k ≅ 𝟭 A :=
  NatIso.ofComponents (fun B ↦ objIso B k) (fun f ↦ objIso.hom_naturality k f)

/-- The component of the canonical lower-face degreewise comparison is `objIso`. -/
@[simp, stacks 0199 "canonical Eilenberg-MacLane lower-face comparison component"]
theorem evalIso_app (k : ℕ) (B : A) :
    (evalIso (A := A) k).app B = objIso B k := sorry

/-- Away from degree `k`, the lower-face normalized terms of the canonical Eilenberg-MacLane
functor are zero. -/
@[stacks 0199 "canonical Eilenberg-MacLane lower-face off-degree vanishing"]
theorem isZero_comp_eval (k i : ℕ) (h : i ≠ k) :
    IsZero
      ((eilenbergMacLane.functor k ⋙
        AlgebraicTopology.normalizedMooreComplex.lowerFace) ⋙
        HomologicalComplex.eval A (ComplexShape.down ℕ) i) := sorry

/-- Away from degree `k`, the lower-face normalized term of `K(B, k)` is zero. -/
@[stacks 0199 "canonical Eilenberg-MacLane lower-face object off-degree vanishing"]
theorem isZero (B : A) (k i : ℕ) (h : i ≠ k) :
    IsZero
      (((AlgebraicTopology.normalizedMooreComplex.lowerFace (A := A)).obj
        (eilenbergMacLane B k)).X i) := sorry

end CategoryTheory.SimplicialObject.eilenbergMacLane.normalizedMoore.lowerFace
