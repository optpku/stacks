module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Morphism.Transport

@[expose] public section

/-!
# Tails of Postnikov-System Morphisms

This leaf restricts a morphism of finite Postnikov systems to their recursive
tails and records its component and functoriality computations.
-/

open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.PostnikovSystem.Morphism

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- Restrict a morphism of Postnikov systems to their recursive tails. Its auxiliary-object maps
are the successor components of the original morphism. -/
@[stacks 0D7Z "tail of a Postnikov-system morphism"]
def tail
    {n : ℕ} {X X' : ComposableArrows D (n + 1)} {P : PostnikovSystem X}
    {P' : PostnikovSystem X'} {φ : X ⟶ X'} (ψ : PostnikovSystem.Morphism P P' φ) :
    PostnikovSystem.Morphism P.tail P'.tail (ComposableArrows.δ₀Functor.map φ) :=
  { yMap := fun i ↦ ψ.yMap i.succ
    comm_toX := sorry
    comm_toNext := sorry
    comm_connecting := sorry }

/-- Restriction to recursive tails shifts the auxiliary-object component index by one. -/
@[stacks 0D7Z, simp]
theorem tail_yMap
    {n : ℕ} {X X' : ComposableArrows D (n + 1)} {P : PostnikovSystem X}
    {P' : PostnikovSystem X'} {φ : X ⟶ X'} (ψ : PostnikovSystem.Morphism P P' φ)
    (i : Fin (n + 1)) :
    (tail ψ).yMap i = ψ.yMap i.succ := sorry

/-- Taking tails commutes with transport along an equality of underlying row maps. -/
@[simp, stacks 0D7Z]
theorem tail_changeBase
    {n : ℕ} {X X' : ComposableArrows D (n + 1)} {P : PostnikovSystem X}
    {P' : PostnikovSystem X'} {φ φ' : X ⟶ X'} (h : φ = φ')
    (ψ : PostnikovSystem.Morphism P P' φ) :
    tail (changeBase h ψ) =
      changeBase (congrArg (ComposableArrows.δ₀Functor (C := D) (n := n)).map h) (tail ψ) := sorry

/-- Taking the tail of an identity gives the identity after transport along functoriality of
the underlying row truncation. -/
@[simp, stacks 0D7Z]
theorem tail_id {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X) :
    changeBase ((ComposableArrows.δ₀Functor (C := D) (n := n)).map_id X)
      (tail (id P)) = id P.tail := sorry

/-- Taking tails preserves composition after transport along functoriality of the underlying
row truncation. -/
@[simp, stacks 0D7Z]
theorem tail_comp
    {n : ℕ} {X X' X'' : ComposableArrows D (n + 1)}
    {P : PostnikovSystem X} {P' : PostnikovSystem X'} {P'' : PostnikovSystem X''}
    {φ : X ⟶ X'} {φ' : X' ⟶ X''}
    (ψ : PostnikovSystem.Morphism P P' φ) (χ : PostnikovSystem.Morphism P' P'' φ') :
    changeBase ((ComposableArrows.δ₀Functor (C := D) (n := n)).map_comp φ φ')
      (tail (comp ψ χ)) = comp (tail ψ) (tail χ) := sorry

end CategoryTheory.PostnikovSystem.Morphism
