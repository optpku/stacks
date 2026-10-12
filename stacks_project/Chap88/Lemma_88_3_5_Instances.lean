/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import stacks_project.Chap88.«88_2_0_2_TopologicallyFiniteType»

/-!
# Topologically finite type over an extended ideal

If `B → C` is a morphism of objects of `C'` over `(A, I)`, then `C` is
topologically of finite type over the pair `(B, I B)`.
-/

@[expose] public section

universe u

namespace Algebra.TopologicallyFiniteType

variable {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]

/-- `I`-adic completeness of a topologically finite type algebra is equivalent
to completeness along the extended ideal `I C`. -/
instance instMapAlgebraMap (I : Ideal A) [TopologicallyFiniteType I C] :
    IsAdicComplete (I.map (algebraMap A C)) C :=
  (IsAdicComplete.map_algebraMap_iff (R := A) (S := C) (M := C) I).mpr inferInstance

variable {B : Type u} [CommRing B] [Algebra A B] [Algebra B C] [IsScalarTower A B C]

/-- A morphism of objects of `C'` over `(A, I)` makes `C` an object of the
corresponding category over `(B, I B)`. -/
instance instMapIdeal (I : Ideal A)
    [TopologicallyFiniteType I B] [TopologicallyFiniteType I C] :
    TopologicallyFiniteType (I.map (algebraMap A B)) C := sorry

/-- Topological finite type of `C` over `I B` unpacks as `I B`-adic completeness
together with finite type of the special fiber `C ⧸ I B C` over `B ⧸ I B`. -/
theorem instMapIdeal_iff (I : Ideal A)
    [TopologicallyFiniteType I B] [TopologicallyFiniteType I C] :
    TopologicallyFiniteType (I.map (algebraMap A B)) C ↔
      IsAdicComplete (I.map (algebraMap A B)) C ∧
        FiniteType (B ⧸ I.map (algebraMap A B))
          (C ⧸ (I.map (algebraMap A B)).map (algebraMap B C)) := sorry

/-- A morphism of objects of `C'` over `(A, I)` makes `C` complete along `I B`
with special fiber of finite type over `B ⧸ I B`. -/
theorem instMapIdeal_spec (I : Ideal A)
    [TopologicallyFiniteType I B] [TopologicallyFiniteType I C] :
    IsAdicComplete (I.map (algebraMap A B)) C ∧
      FiniteType (B ⧸ I.map (algebraMap A B))
        (C ⧸ (I.map (algebraMap A B)).map (algebraMap B C)) := sorry

end Algebra.TopologicallyFiniteType
