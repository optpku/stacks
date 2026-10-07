module

public import stacks_project.Chap88.Definition_88_21_1_Formal

/-!
# McQuillan affine formal algebraic spaces, functor of points

A functor of points on schemes over `S` is a McQuillan affine formal algebraic
space when some directed affine thickening presentation has surjective
inverse-limit projections on global sections. This owner lives on the Chap88
carrier `(Over S)ᵒᵖ ⥤ Type u` so it can be imported beside closed immersions
without the Chap87 Types duplicate of `IsFormalAlgebraicSpace`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- A functor of points on schemes over `S` is a McQuillan affine formal
algebraic space when some directed affine thickening presentation has
surjective inverse-limit projections on global sections. -/
@[mk_iff]
class IsMcQuillanAffine {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) : Prop where
  /-- There is a directed affine thickening presentation whose inverse-limit
  projections on global sections are surjective. -/
  exists_surjective_limit_colimit :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
      IsDirectedAffineThickeningColimit D X ∧
        ∀ (i : Λ) (x : (Γ((D.obj i).left, ⊤) : Type u)),
          ∃ s : (j : Λ) → (Γ((D.obj j).left, ⊤) : Type u),
            (∀ {j k : Λ} (f : j ⟶ k), (D.map f).left.appTop (s k) = s j) ∧
              s i = x

namespace IsMcQuillanAffine

/-- A McQuillan affine formal algebraic space admits a directed thickening
presentation with surjective inverse-limit projections on global sections. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) [IsMcQuillanAffine X] :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
      IsDirectedAffineThickeningColimit D X ∧
        ∀ (i : Λ) (x : (Γ((D.obj i).left, ⊤) : Type u)),
          ∃ s : (j : Λ) → (Γ((D.obj j).left, ⊤) : Type u),
            (∀ {j k : Λ} (f : j ⟶ k), (D.map f).left.appTop (s k) = s j) ∧
              s i = x :=
  sorry

/-- A functor of points is a McQuillan affine formal algebraic space if and
only if some directed affine thickening presentation has surjective
inverse-limit projections on global sections. -/
theorem iff {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) :
    IsMcQuillanAffine X ↔
      ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
        IsDirectedAffineThickeningColimit D X ∧
          ∀ (i : Λ) (x : (Γ((D.obj i).left, ⊤) : Type u)),
            ∃ s : (j : Λ) → (Γ((D.obj j).left, ⊤) : Type u),
              (∀ {j k : Λ} (f : j ⟶ k), (D.map f).left.appTop (s k) = s j) ∧
                s i = x :=
  sorry

/-- The representable functor of an affine scheme over `S` is a McQuillan
affine formal algebraic space, via the constant directed system. -/
instance instYoneda {S : Scheme.{u}} (U : Over S) [IsAffine U.left] :
    IsMcQuillanAffine (yoneda.obj U) :=
  sorry

end IsMcQuillanAffine

end AlgebraicGeometry.FormalAlgebraicSpace
