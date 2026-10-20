module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism

/-!
# Surjectivity on algebraically closed field-valued points

A morphism of algebraic spaces over a scheme is surjective on algebraically
closed field-valued points when postcomposition is surjective over every
algebraically closed field equipped with a morphism to the base scheme.
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
  Iff.rfl

namespace surjectiveOnAlgClosedPoints

/-- Surjectivity of postcomposition on algebraically closed field-valued points
implies `surjectiveOnAlgClosedPoints`. -/
theorem of
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] (σ : Spec (.of k) ⟶ S),
      Function.Surjective (fun x : ofOver (Over.mk σ) ⟶ X ↦ x ≫ f)) :
    surjectiveOnAlgClosedPoints f :=
  h

/-- Surjectivity on algebraically closed field-valued points gives surjectivity
of postcomposition on `Mor_S(Spec k, X)` for each algebraically closed field
`k` over `S`. -/
theorem spec (h : surjectiveOnAlgClosedPoints f) (k : Type u) [Field k]
    [IsAlgClosed k] (σ : Spec (.of k) ⟶ S) :
    Function.Surjective (fun x : ofOver (Over.mk σ) ⟶ X ↦ x ≫ f) :=
  h k σ

end surjectiveOnAlgClosedPoints

end AlgebraicGeometry.AlgebraicSpace
