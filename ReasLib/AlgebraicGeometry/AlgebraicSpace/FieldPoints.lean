module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism

/-!
# Injectivity on field-valued points of algebraic spaces

A morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` is injective on
field-valued points when, for every field `K` over `S`, postcomposition with `f`
is injective on `Mor_S(Spec K, X)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- A morphism of algebraic spaces over `S` is injective on field-valued points if
for every field `K` over `S`, postcomposition with `f` is injective on
`Mor_S(Spec K, X)`. -/
def injectiveOnFieldPoints : Prop :=
  ∀ (K : Type u) [Field K] (σ : Spec (.of K) ⟶ S),
    Function.Injective (fun x : ofOver (Over.mk σ) ⟶ X ↦ x ≫ f)

/-- A morphism is injective on field-valued points if and only if postcomposition
is injective on `Mor_S(Spec K, X)` for every field `K` over `S`. -/
theorem injectiveOnFieldPoints_iff :
    injectiveOnFieldPoints f ↔
      ∀ (K : Type u) [Field K] (σ : Spec (.of K) ⟶ S),
        Function.Injective (fun x : ofOver (Over.mk σ) ⟶ X ↦ x ≫ f) := sorry

namespace injectiveOnFieldPoints

/-- Injectivity of postcomposition on field-valued points implies
`injectiveOnFieldPoints`. -/
theorem of
    (h : ∀ (K : Type u) [Field K] (σ : Spec (.of K) ⟶ S),
      Function.Injective (fun x : ofOver (Over.mk σ) ⟶ X ↦ x ≫ f)) :
    injectiveOnFieldPoints f := sorry

/-- `injectiveOnFieldPoints` implies injectivity of postcomposition on
`Mor_S(Spec K, X)` for every field `K` over `S`. -/
theorem spec (h : injectiveOnFieldPoints f) (K : Type u) [Field K]
    (σ : Spec (.of K) ⟶ S) :
    Function.Injective (fun x : ofOver (Over.mk σ) ⟶ X ↦ x ≫ f) := sorry

end injectiveOnFieldPoints

end AlgebraicGeometry.AlgebraicSpace
