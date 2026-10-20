module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.McQuillan
public import stacks_project.Chap88.Definition_88_21_1_Formal

/-!
# McQuillan affine formal algebraic spaces, functor of points

The McQuillan predicate and its directed affine thickening characterization
are provided by the shared formal algebraic space API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FormalAlgebraicSpace

universe u

#check (AlgebraicGeometry.FormalAlgebraicSpace.IsMcQuillanAffine :
    ∀ {S : Scheme.{u}}, ((Over S)ᵒᵖ ⥤ Type u) → Prop)

#check (AlgebraicGeometry.FormalAlgebraicSpace.IsMcQuillanAffine.spec :
    ∀ {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) [IsMcQuillanAffine X],
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
      IsDirectedAffineThickeningColimit D X ∧
        ∀ (i : Λ) (x : (Γ((D.obj i).left, ⊤) : Type u)),
          ∃ s : (j : Λ) → (Γ((D.obj j).left, ⊤) : Type u),
            (∀ {j k : Λ} (f : j ⟶ k), (D.map f).left.appTop (s k) = s j) ∧
              s i = x)

#check (AlgebraicGeometry.FormalAlgebraicSpace.IsMcQuillanAffine.iff :
    ∀ {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u),
    IsMcQuillanAffine X ↔
      IsFormalAlgebraicSpace X ∧
      ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
        IsDirectedAffineThickeningColimit D X ∧
          ∀ (i : Λ) (x : (Γ((D.obj i).left, ⊤) : Type u)),
            ∃ s : (j : Λ) → (Γ((D.obj j).left, ⊤) : Type u),
              (∀ {j k : Λ} (f : j ⟶ k), (D.map f).left.appTop (s k) = s j) ∧
                s i = x)

#check (AlgebraicGeometry.FormalAlgebraicSpace.IsMcQuillanAffine.instYoneda :
    ∀ {S : Scheme.{u}} (U : Over S) [IsAffine U.left],
      IsMcQuillanAffine (yoneda.obj U))
