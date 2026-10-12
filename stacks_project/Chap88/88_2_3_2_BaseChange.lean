/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommAlgCat.TopologicallyFiniteType.BaseChange

@[expose] public section

open CategoryTheory TensorProduct

open scoped TensorProduct

universe u

variable {A1 A2 : Type u} [CommRing A1] [CommRing A2] [Algebra A1 A2]

#check (Algebra.TopologicallyFiniteType.tensorExtensionIdeal :
  ∀ (I2 : Ideal A2) (B : Type u) [CommRing B] [Algebra A1 B],
    Ideal (B ⊗[A1] A2))
#check (Algebra.TopologicallyFiniteType.completedBaseChange :
  ∀ (A1 : Type u) {A2 : Type u} [CommRing A1] [CommRing A2] [Algebra A1 A2],
    Ideal A2 → (B : Type u) → [CommRing B] → [Algebra A1 B] → Type u)
#check (Algebra.TopologicallyFiniteType.completedBaseChangeMap :
  ∀ (I2 : Ideal A2) {B B' : Type u} [CommRing B] [CommRing B'] [Algebra A1 B]
    [Algebra A1 B'], (B →ₐ[A1] B') →
      Algebra.TopologicallyFiniteType.completedBaseChange A1 I2 B →ₐ[A2]
        Algebra.TopologicallyFiniteType.completedBaseChange A1 I2 B')
#check (Algebra.TopologicallyFiniteType.completedBaseChange_topologicallyFiniteType :
  ∀ (I2 : Ideal A2) (I1 : Ideal A1) {c : ℕ}, 1 ≤ c →
    I1.map (algebraMap A1 A2) ^ c ≤ I2 → I2.FG →
      ∀ {B : Type u} [CommRing B] [Algebra A1 B],
        Algebra.TopologicallyFiniteType I1 B →
          Algebra.TopologicallyFiniteType I2
            (Algebra.TopologicallyFiniteType.completedBaseChange A1 I2 B))
#check (CommAlgCat.TopologicallyFiniteType.baseChange :
  ∀ (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ}, 1 ≤ c →
    I1.map (algebraMap A1 A2) ^ c ≤ I2 → I2.FG →
      CommAlgCat.TopologicallyFiniteType.{u} A1 I1 ⥤
        CommAlgCat.TopologicallyFiniteType.{u} A2 I2)
