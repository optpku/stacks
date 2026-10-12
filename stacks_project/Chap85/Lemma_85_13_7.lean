/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_13_2_System

/-!
# Lemma 85.13.7

In Situation 85.3.3, a cartesian simplicial system of the derived category with
vanishing `Hom(K_i⟦t⟧, K_i)` for `t > 0` comes from a cartesian object of
`D(C_total)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.SimplicialSites

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instMorphismDiagram : IsMorphismDiagram C J]
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
include instMorphismDiagram instWeakSheafify instLeftKan
variable [UnivLE.{max u v, w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]

/-- Lemma 85.13.7
In Situation 85.3.3, let `(K_n, K_φ)` be a cartesian simplicial system of the
derived category such that `Hom(K_i⟦t⟧, K_i) = 0` for every stage `i` and every
`t > 0`. Then there exists a cartesian object `K` of `D(C_total)` whose
associated simplicial system is isomorphic to `(K_n, K_φ)`. -/
@[stacks 0D9L]
theorem exists_isCartesian_of_derivedSystem
    (Ksys : DerivedAbelianSystemOnComponents C J)
    [DerivedAbelianSystem.IsCartesian Ksys]
    (h_hom : ∀ (n : SimplexCategory) (t : ℤ), 0 < t →
      Subsingleton ((Ksys.obj n)⟦t⟧ ⟶ Ksys.obj n)) :
    ∃ (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
      (α : DerivedAbelianSystem.Hom (toDerivedSystem C J K) Ksys),
      Derived.IsCartesian C J K ∧ ∀ n, IsIso (α.app n) :=
  sorry

end CategoryTheory.SimplicialSites
