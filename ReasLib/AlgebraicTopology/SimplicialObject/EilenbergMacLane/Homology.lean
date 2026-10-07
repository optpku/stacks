module

public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import ReasLib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import ReasLib.AlgebraicTopology.SimplicialObject.EilenbergMacLane.NormalizedMoore
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Homology of Eilenberg--MacLane simplicial objects

@stack 0197

The normalized Moore complex of `K(A, k)` is the single complex concentrated in degree `k`.
Combining this comparison with the canonical Dold--Kan homotopy equivalence computes the homology
of the alternating face map complex as well.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open AlgebraicTopology.DoldKan Abelian.DoldKan HomologicalComplex
open scoped Simplicial DoldKan

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.eilenbergMacLane

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace homology

/-- For fixed Eilenberg--MacLane degree `k` and homological degree `i`, the homology of the
alternating face map complex is a functor of the coefficient object. -/
@[stacks 0197 "Eilenberg-MacLane alternating-face homology functor"]
noncomputable abbrev functor (k i : ℕ) : A ⥤ A :=
  eilenbergMacLane.functor k ⋙ AlgebraicTopology.alternatingFaceMapComplex A ⋙
    HomologicalComplex.homologyFunctor A (ComplexShape.down ℕ) i

/-- Evaluating `functor k i` at `B` gives the degree-`i` homology of the alternating face map
complex of `K(B, k)`. -/
@[simp, stacks 0197 "Eilenberg-MacLane homology functor object formula"]
theorem functor_obj (k i : ℕ) (B : A) :
    (functor (A := A) k i).obj B = K[eilenbergMacLane B k].homology i := sorry

/-- The map of `functor k i` is the homology map induced by the Eilenberg--MacLane map on
alternating face map complexes. -/
@[simp, stacks 0197 "Eilenberg-MacLane homology functor map formula"]
theorem functor_map (k i : ℕ) {B D : A} (f : B ⟶ D) :
    (functor (A := A) k i).map f =
      HomologicalComplex.homologyMap
        ((AlgebraicTopology.alternatingFaceMapComplex A).map
          ((eilenbergMacLane.functor k).map f)) i := sorry

/-- Degree-`k` homology of the alternating face map complex of `K(B, k)` is canonically
isomorphic to `B`. -/
@[stacks 0197 "homology of an Eilenberg-MacLane object"]
noncomputable def objIso (B : A) (k : ℕ) :
    (functor (A := A) k k).obj B ≅ B :=
  ((AlgebraicTopology.DoldKan.mooreEquiv
      (A := A) (Y := eilenbergMacLane B k)).toHomologyIso k).symm ≪≫
    (homologyFunctor A (ComplexShape.down ℕ) k).mapIso
      ((normalizedMoore.iso (A := A) k).app B) ≪≫
    singleObjHomologySelfIso (ComplexShape.down ℕ) k B

/-- The degree-`k` objectwise homology comparisons are natural in the coefficient object. -/
@[stacks 0197 "Eilenberg-MacLane homology comparison naturality"]
theorem objIso.hom_naturality (k : ℕ) {B D : A} (f : B ⟶ D) :
    (functor (A := A) k k).map f ≫ (objIso D k).hom =
      (objIso B k).hom ≫ f := sorry

/-- The inverse degree-`k` homology comparisons are natural in the coefficient object. -/
@[stacks 0197 "inverse Eilenberg-MacLane homology comparison naturality"]
theorem objIso.inv_naturality (k : ℕ) {B D : A} (f : B ⟶ D) :
    f ≫ (objIso D k).inv =
      (objIso B k).inv ≫ (functor (A := A) k k).map f := sorry

/-- Degree-`k` homology of the alternating face map complex of the Eilenberg--MacLane functor
is naturally isomorphic to the identity functor. -/
@[stacks 0197 "functorial Eilenberg-MacLane homology computation"]
noncomputable def evalIso (k : ℕ) : functor (A := A) k k ≅ 𝟭 A :=
  NatIso.ofComponents (fun B ↦ objIso B k) (fun f ↦ objIso.hom_naturality k f)

/-- The component of the functorial degree-`k` homology comparison is `objIso`. -/
@[simp, stacks 0197 "functorial Eilenberg-MacLane homology component formula"]
theorem evalIso_app (k : ℕ) (B : A) :
    (evalIso (A := A) k).app B = objIso B k := sorry

/-- Away from degree `k`, the homology of the alternating face map complex of the
Eilenberg--MacLane functor is the zero functor. -/
@[stacks 0197 "functorial off-degree Eilenberg-MacLane homology vanishing"]
theorem isZeroFunctor (k i : ℕ) (h : i ≠ k) :
    IsZero (functor (A := A) k i) := sorry

/-- Away from degree `k`, the alternating face map complex of `K(B, k)` has zero homology. -/
@[stacks 0197 "off-degree Eilenberg-MacLane homology vanishing"]
theorem isZero (B : A) (k i : ℕ) (h : i ≠ k) :
    IsZero (K[eilenbergMacLane B k].homology i) := sorry

end homology

end CategoryTheory.SimplicialObject.eilenbergMacLane
