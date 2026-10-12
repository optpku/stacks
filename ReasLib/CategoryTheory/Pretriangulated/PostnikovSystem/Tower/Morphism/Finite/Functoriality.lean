/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Morphism.Transport
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Morphism.Finite.System

/-!
# Functoriality of Finite Postnikov-Tower Restrictions

This leaf records identity and composition laws for finite-system restriction,
transported along the corresponding laws for the underlying finite rows.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.PostnikovSystem.Tower.Hom

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
variable {T T' T'' : Tower D}

/-- Finite-system restriction preserves identities after transport of the underlying row map. -/
@[simp, stacks 0D8Z]
theorem id_finite (T : Tower D) (n : ℕ) :
    PostnikovSystem.Morphism.changeBase (id_row T n) (finite (id T) n) =
      PostnikovSystem.Morphism.id (T.finite n) := sorry

/-- Finite-system restriction preserves composition after transport of the underlying row map. -/
@[simp, stacks 0D8Z]
theorem comp_finite (f : Hom T T') (g : Hom T' T'') (n : ℕ) :
    PostnikovSystem.Morphism.changeBase (comp_row f g n) (finite (comp f g) n) =
      PostnikovSystem.Morphism.comp (finite f n) (finite g n) := sorry

end CategoryTheory.PostnikovSystem.Tower.Hom
