module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver

/-!
# Surjectivity on algebraically closed field-valued points

A morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` is surjective on
algebraically closed field-valued points when, for every algebraically closed
field `k` over `S`, postcomposition with `f` is surjective on `Mor_S(Spec k, X)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- A morphism of algebraic spaces over `S` is surjective on algebraically
closed field-valued points if for every algebraically closed field `k` over `S`,
postcomposition with `f` is surjective on `Mor_S(Spec k, X)`. -/
def surjectiveOnAlgClosedPoints : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (σ : Spec (.of k) ⟶ S),
    Function.Surjective (fun x : ofOver (Over.mk σ) ⟶ X ↦ x ≫ f)

/-- A morphism is surjective on algebraically closed field-valued points if and
only if postcomposition is surjective on `Mor_S(Spec k, X)` for every
algebraically closed field `k` over `S`. -/
theorem surjectiveOnAlgClosedPoints_iff :
    surjectiveOnAlgClosedPoints f ↔
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (σ : Spec (.of k) ⟶ S),
        Function.Surjective (fun x : ofOver (Over.mk σ) ⟶ X ↦ x ≫ f) :=
  sorry

namespace surjectiveOnAlgClosedPoints

/-- Surjectivity of postcomposition on algebraically closed field-valued points
implies `surjectiveOnAlgClosedPoints`. -/
theorem of
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] (σ : Spec (.of k) ⟶ S),
      Function.Surjective (fun x : ofOver (Over.mk σ) ⟶ X ↦ x ≫ f)) :
    surjectiveOnAlgClosedPoints f :=
  sorry

/-- `surjectiveOnAlgClosedPoints` implies surjectivity of postcomposition on
`Mor_S(Spec k, X)` for every algebraically closed field `k` over `S`. -/
theorem spec (h : surjectiveOnAlgClosedPoints f) (k : Type u) [Field k]
    [IsAlgClosed k] (σ : Spec (.of k) ⟶ S) :
    Function.Surjective (fun x : ofOver (Over.mk σ) ⟶ X ↦ x ≫ f) :=
  sorry

end surjectiveOnAlgClosedPoints

end AlgebraicGeometry.AlgebraicSpace
