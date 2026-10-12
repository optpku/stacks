/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology
public import Mathlib.Algebra.Algebra.Hom

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.ChowCohomology

variable {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
variable {X Y Z : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S} {r : Z ⟶ S}
variable [LocallyOfFiniteType p] [LocallyOfFiniteType q]

/-- Restriction along an over-morphism sends the zero identity bivariant class to zero. -/
theorem restrictClass_zero (f : Over.mk p ⟶ Over.mk q) (n : ℤ) :
    BivariantClass.restrict delta f (𝟙 (Over.mk p)) f IsPullback.of_id_snd n
        (0 : degree delta q n) = 0 := sorry

/-- Restriction along an over-morphism preserves addition of identity bivariant classes. -/
theorem restrictClass_add (f : Over.mk p ⟶ Over.mk q) (n : ℤ) (a b : degree delta q n) :
    BivariantClass.restrict delta f (𝟙 (Over.mk p)) f IsPullback.of_id_snd n (a + b) =
      BivariantClass.restrict delta f (𝟙 (Over.mk p)) f IsPullback.of_id_snd n a +
        BivariantClass.restrict delta f (𝟙 (Over.mk p)) f IsPullback.of_id_snd n b := sorry

/-- Restriction of identity bivariant classes in degree `n` along an over-morphism. -/
def restrictDegree (f : Over.mk p ⟶ Over.mk q) (n : ℤ) :
    degree delta q n →+ degree delta p n where
  toFun := BivariantClass.restrict delta f (𝟙 (Over.mk p)) f IsPullback.of_id_snd n
  map_zero' := restrictClass_zero delta f n
  map_add' := restrictClass_add delta f n

/-- Homogeneous restriction is the identity-square specialization of bivariant
restriction. -/
theorem restrictDegree_apply (f : Over.mk p ⟶ Over.mk q) (n : ℤ) (a : degree delta q n) :
    restrictDegree delta f n a =
      BivariantClass.restrict delta f (𝟙 (Over.mk p)) f IsPullback.of_id_snd n a := sorry

/-- Homogeneous restriction sends the graded unit to the unit of Chow cohomology. -/
theorem restrictOne (f : Over.mk p ⟶ Over.mk q) :
    ((DirectSum.of (degree delta p) 0).comp (restrictDegree delta f 0))
        (GradedMonoid.GOne.one : degree delta q 0) =
      (1 : ring delta p) := sorry

/-- Homogeneous restriction preserves the product of identity bivariant classes. -/
theorem restrictMul (f : Over.mk p ⟶ Over.mk q) {i j : ℤ}
    (a : degree delta q i) (b : degree delta q j) :
    ((DirectSum.of (degree delta p) (i + j)).comp
        (restrictDegree delta f (i + j))) (GradedMonoid.GMul.mul a b) =
      ((DirectSum.of (degree delta p) i).comp (restrictDegree delta f i)) a *
        ((DirectSum.of (degree delta p) j).comp (restrictDegree delta f j)) b := sorry

/-- The canonical contravariant `ℤ`-algebra homomorphism on Chow cohomology induced by
an over-morphism. -/
def restrict (f : Over.mk p ⟶ Over.mk q) : ring delta q →ₐ[ℤ] ring delta p :=
  (DirectSum.toSemiring
    (fun n ↦ (DirectSum.of (degree delta p) n).comp (restrictDegree delta f n))
    (restrictOne delta f) (restrictMul delta f)).toIntAlgHom

/-- The Chow-cohomology restriction map acts on a homogeneous class by homogeneous
restriction. -/
theorem restrict_of (f : Over.mk p ⟶ Over.mk q) (n : ℤ) (a : degree delta q n) :
    restrict delta f (DirectSum.of (degree delta q) n a) =
      DirectSum.of (degree delta p) n (restrictDegree delta f n a) := sorry

/-- Restriction along an identity over-morphism is the identity algebra homomorphism. -/
theorem restrict_id (p : X ⟶ S) [LocallyOfFiniteType p] :
    restrict delta (𝟙 (Over.mk p)) = AlgHom.id ℤ (ring delta p) := sorry

/-- Chow-cohomology restriction is contravariantly functorial under composition. -/
theorem restrict_comp [LocallyOfFiniteType r]
    (f : Over.mk p ⟶ Over.mk q) (g : Over.mk q ⟶ Over.mk r) :
    restrict delta (f ≫ g) = (restrict delta f).comp (restrict delta g) := sorry

end AlgebraicGeometry.ChowCohomology
