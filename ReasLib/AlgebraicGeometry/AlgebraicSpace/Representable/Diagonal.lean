module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces

/-- A morphism of presheaves representable by algebraic spaces has a relative diagonal
representable by algebraic spaces. -/
theorem pullback_diagonal {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    [HasPullback a a] (ha : representableByAlgebraicSpaces a) :
    representableByAlgebraicSpaces (pullback.diagonal a) := sorry

/-- The diagonal of a presheaf on schemes over `S` is representable by algebraic
spaces if and only if every map from a scheme over `S` to the presheaf is
representable by algebraic spaces. -/
theorem diag_iff {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} :
    representableByAlgebraicSpaces (diag F) ↔
      ∀ ⦃T : Over S⦄ (a : yoneda.obj T ⟶ F), representableByAlgebraicSpaces a :=
  sorry

/-- The diagonal of a presheaf on schemes over `S` is representable by algebraic
spaces if and only if every map from an algebraic space over `S` to the presheaf
is representable by algebraic spaces. -/
theorem diag_iff_isAlgebraicSpace {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} :
    representableByAlgebraicSpaces (diag F) ↔
      ∀ ⦃X : (Over S)ᵒᵖ ⥤ Type u⦄ [IsAlgebraicSpace X] (a : X ⟶ F),
        representableByAlgebraicSpaces a :=
  sorry

/-- If the diagonal of a presheaf is representable by algebraic spaces, then every
map from a scheme over `S` to that presheaf is representable by algebraic
spaces. -/
theorem of_diag {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} (h : representableByAlgebraicSpaces (diag F))
    ⦃T : Over S⦄ (a : yoneda.obj T ⟶ F) :
    representableByAlgebraicSpaces a :=
  (diag_iff.mp h) a

/-- If the diagonal of a presheaf is representable by algebraic spaces, then every
map from an algebraic space over `S` to that presheaf is representable by
algebraic spaces. -/
theorem of_diag_isAlgebraicSpace {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} (h : representableByAlgebraicSpaces (diag F))
    ⦃X : (Over S)ᵒᵖ ⥤ Type u⦄ [IsAlgebraicSpace X] (a : X ⟶ F) :
    representableByAlgebraicSpaces a :=
  (diag_iff_isAlgebraicSpace.mp h) a

/-- If every map from a scheme over `S` to a presheaf is representable by
algebraic spaces, then the diagonal of that presheaf is representable by
algebraic spaces. -/
theorem diag_of_yoneda {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u}
    (h : ∀ ⦃T : Over S⦄ (a : yoneda.obj T ⟶ F), representableByAlgebraicSpaces a) :
    representableByAlgebraicSpaces (diag F) :=
  diag_iff.mpr h

/-- A morphism of presheaves is representable by algebraic spaces if its composite
with a second morphism and the relative diagonal of the second morphism are
representable by algebraic spaces. -/
@[stacks 0AMN]
theorem of_comp {S : Scheme.{u}}
    {F G H : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : G ⟶ H)
    [HasPullback b b] (hΔ : representableByAlgebraicSpaces (pullback.diagonal b))
    (hab : representableByAlgebraicSpaces (a ≫ b)) :
    representableByAlgebraicSpaces a :=
  sorry

/-- Representability by algebraic spaces cancels against postcomposition when the
relative diagonal of the second map is representable by algebraic spaces. -/
instance hasOfPostcompProperty_diagonal
    {S : Scheme.{u}} [HasPullbacks ((Over S)ᵒᵖ ⥤ Type u)] :
    (@representableByAlgebraicSpaces S).HasOfPostcompProperty
      (@representableByAlgebraicSpaces S).diagonal :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces
