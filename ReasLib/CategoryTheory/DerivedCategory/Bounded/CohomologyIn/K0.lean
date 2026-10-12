/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Bounded.K0
public import ReasLib.CategoryTheory.DerivedCategory.Bounded.CohomologyIn
public import ReasLib.CategoryTheory.Pretriangulated.K0.Euler
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Grothendieck Groups of Bounded Cohomology-In Subcategories

For a weak Serre object property `P`, the degree-zero embedding and the
cohomological Euler characteristic identify `AbelianK0 P.FullSubcategory`
with the triangulated Grothendieck group of
`DerivedCategory.Bounded.CohomologyIn P`.
-/

open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open scoped BigOperators

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.Bounded.CohomologyIn.K0

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
variable (P : ObjectProperty A) [IsWeakSerreClass P]

/-- Short-exact relations in `P.FullSubcategory` are killed by the
degree-zero embedding. -/
theorem relations_le_ker_fromAbelian :
    AbelianK0.relations P.FullSubcategory ≤
      (FreeAbelianGroup.lift fun X : P.FullSubcategory ↦
        TriangulatedK0.of ((Single.functor P).obj X)).ker := sorry

/-- The degree-zero embedding induces a homomorphism from abelian `K₀` to
the triangulated `K₀` of bounded objects with cohomology in `P`. -/
@[stacks 0FCS]
noncomputable def fromAbelian :
    AbelianK0 P.FullSubcategory →+
      TriangulatedK0 (DerivedCategory.Bounded.CohomologyIn P) :=
  AbelianK0.lift
    (fun X : P.FullSubcategory ↦ TriangulatedK0.of ((Single.functor P).obj X))
    (relations_le_ker_fromAbelian P)

/-- The degree-zero map sends an object class to the class of its lifted
degree-zero derived object. -/
@[stacks 0FCS, simp]
theorem fromAbelian_of (X : P.FullSubcategory) :
    fromAbelian P (AbelianK0.of X) =
      TriangulatedK0.of ((Single.functor P).obj X) := sorry

namespace Euler

/-- The Euler class of a bounded object with cohomology in `P`, expressed as
the finite alternating sum of its lifted cohomology objects. -/
@[stacks 0FCS]
noncomputable def value (X : DerivedCategory.Bounded.CohomologyIn P) :
    AbelianK0 P.FullSubcategory :=
  ∑ᶠ i : ℤ, i.negOnePow • AbelianK0.of ((Homology.functor P i).obj X)

end Euler

/-- The cohomological Euler characteristic from triangulated `K₀` to the
abelian `K₀` of `P.FullSubcategory`. -/
@[stacks 0FCS]
noncomputable def toAbelian :
    TriangulatedK0 (DerivedCategory.Bounded.CohomologyIn P) →+
      AbelianK0 P.FullSubcategory :=
  (Homology.functor P 0).eulerK0Map (Homology.hasFiniteSupport P)

/-- The Euler homomorphism evaluates on an object class as the alternating
sum of its lifted cohomology classes. -/
@[stacks 0FCS, simp]
theorem toAbelian_of (X : DerivedCategory.Bounded.CohomologyIn P) :
    toAbelian P (TriangulatedK0.of X) = Euler.value P X := sorry

/-- Euler characteristic after the degree-zero embedding is the identity
homomorphism. -/
@[stacks 0FCS]
theorem to_from :
    (toAbelian P).comp (fromAbelian P) =
      AddMonoidHom.id (AbelianK0 P.FullSubcategory) := sorry

/-- Pointwise computation of Euler characteristic after the degree-zero
embedding. -/
@[simp]
theorem to_from_apply (x : AbelianK0 P.FullSubcategory) :
    toAbelian P (fromAbelian P x) = x := sorry

/-- The degree-zero embedding after Euler characteristic is the identity
homomorphism. -/
@[stacks 0FCS]
theorem from_to :
    (fromAbelian P).comp (toAbelian P) =
      AddMonoidHom.id
        (TriangulatedK0 (DerivedCategory.Bounded.CohomologyIn P)) := sorry

/-- Pointwise computation of the degree-zero embedding after Euler
characteristic. -/
@[simp]
theorem from_to_apply
    (x : TriangulatedK0 (DerivedCategory.Bounded.CohomologyIn P)) :
    fromAbelian P (toAbelian P x) = x := sorry

/-- The canonical additive equivalence between the abelian Grothendieck group of a weak Serre
class and the triangulated Grothendieck group of bounded derived objects whose cohomology lies
in that class. -/
@[stacks 0FCS]
noncomputable def equiv :
    AbelianK0 P.FullSubcategory ≃+
      TriangulatedK0 (DerivedCategory.Bounded.CohomologyIn P) where
  toFun := fromAbelian P
  invFun := toAbelian P
  left_inv := DFunLike.congr_fun (to_from P)
  right_inv := DFunLike.congr_fun (from_to P)
  map_add' := (fromAbelian P).map_add

/-- The canonical additive equivalence from the bounded derived category of a weak Serre
subcategory to the bounded ambient derived objects whose cohomology lies in that subcategory. -/
@[stacks 0FDF]
noncomputable def comparisonEquiv [HasDerivedCategory.{w} P.FullSubcategory] :
    TriangulatedK0 (DerivedCategory.Bounded P.FullSubcategory) ≃+
      TriangulatedK0 (DerivedCategory.Bounded.CohomologyIn P) :=
  (DerivedCategory.Bounded.K0.equiv P.FullSubcategory).symm.trans (equiv P)

/-- The canonical equivalence sends an object class to its degree-zero
derived class. -/
@[stacks 0FCS, simp]
theorem equiv_apply_of (X : P.FullSubcategory) :
    equiv P (AbelianK0.of X) =
      TriangulatedK0.of ((Single.functor P).obj X) := sorry

/-- The inverse canonical equivalence sends a derived object class to its
cohomological Euler class. -/
@[stacks 0FCS, simp]
theorem equiv_symm_apply_of
    (X : DerivedCategory.Bounded.CohomologyIn P) :
    (equiv P).symm (TriangulatedK0.of X) = Euler.value P X := sorry

end CategoryTheory.DerivedCategory.Bounded.CohomologyIn.K0
