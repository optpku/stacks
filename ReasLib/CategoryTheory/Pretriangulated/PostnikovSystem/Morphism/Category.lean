module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Morphism.Transport

@[expose] public section

/-!
# Category laws for Postnikov-system morphisms

This leaf records the dependent category laws for morphisms whose underlying finite-row map is
part of the type.  The laws use `changeBase` to transport along the corresponding category law
in the base category.
-/

open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.PostnikovSystem.Morphism

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

variable {n : ℕ}

/- The underlying row maps are indexed in the morphism type, so the ordinary category laws need
   an explicit transport before the two sides can be compared. -/

/-- The canonical identity Postnikov-system morphism is a left identity, after transporting its
underlying row map along `Category.id_comp`. -/
@[simp, stacks 0D7Z]
theorem id_comp {X X' : ComposableArrows D n} {P : PostnikovSystem X}
    {P' : PostnikovSystem X'} {φ : X ⟶ X'}
    (ψ : PostnikovSystem.Morphism P P' φ) :
    changeBase (Category.id_comp φ) (comp (id P) ψ) = ψ := sorry

/-- The canonical identity Postnikov-system morphism is a right identity, after transporting its
underlying row map along `Category.comp_id`. -/
@[simp, stacks 0D7Z]
theorem comp_id {X X' : ComposableArrows D n} {P : PostnikovSystem X}
    {P' : PostnikovSystem X'} {φ : X ⟶ X'}
    (ψ : PostnikovSystem.Morphism P P' φ) :
    changeBase (Category.comp_id φ) (comp ψ (id P')) = ψ := sorry

/-- Composition of Postnikov-system morphisms is associative, after transporting the underlying
row map along `Category.assoc`. -/
@[stacks 0D7Z]
theorem assoc {X X' X'' X''' : ComposableArrows D n}
    {P : PostnikovSystem X} {P' : PostnikovSystem X'} {P'' : PostnikovSystem X''}
    {P''' : PostnikovSystem X'''} {φ : X ⟶ X'} {φ' : X' ⟶ X''} {φ'' : X'' ⟶ X'''}
    (ψ : PostnikovSystem.Morphism P P' φ)
    (χ : PostnikovSystem.Morphism P' P'' φ')
    (ω : PostnikovSystem.Morphism P'' P''' φ'') :
    changeBase (Category.assoc φ φ' φ'') (comp (comp ψ χ) ω) =
      comp ψ (comp χ ω) := sorry

end CategoryTheory.PostnikovSystem.Morphism
