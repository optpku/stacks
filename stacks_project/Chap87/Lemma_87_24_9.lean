/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Definition_88_21_1_Formal

/-!
# Fibre products with locally of finite type morphisms of formal algebraic spaces

The fibre product of a locally of finite type morphism of formal algebraic
spaces with a locally Noetherian object is again locally Noetherian.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace LocallyOfFiniteType

/-- Lemma 87.24.9: Let `S` be a scheme. Let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of formal algebraic spaces over `S`. If `Z` is locally Noetherian
and `f` is locally of finite type, then the fibre product `Z ×_Y X`, realized
as `pullback f g` up to the canonical symmetry of fibre products, is locally
Noetherian. -/
@[stacks 0AQ8]
instance isLocallyNoetherian_pullback {S : Scheme.{u}}
    {X Y Z : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z] (f : X ⟶ Y)
    (g : Z ⟶ Y) [LocallyOfFiniteType f] [IsLocallyNoetherian Z]
    [HasPullback f g] [IsFormalAlgebraicSpace (pullback f g)] :
    IsLocallyNoetherian (pullback f g) :=
  sorry

/-- A fibre product of a locally of finite type morphism of formal algebraic
spaces with a locally Noetherian object is locally Noetherian, for an
arbitrary `IsPullback` square. -/
theorem isLocallyNoetherian_of_isPullback {S : Scheme.{u}}
    {X Y Z P : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    [IsFormalAlgebraicSpace P] {f : X ⟶ Y} {g : Z ⟶ Y} {pX : P ⟶ X}
    {pZ : P ⟶ Z} (sq : IsPullback pX pZ f g) [LocallyOfFiniteType f]
    [IsLocallyNoetherian Z] : IsLocallyNoetherian P :=
  sorry

end LocallyOfFiniteType

end AlgebraicGeometry.FormalAlgebraicSpace
