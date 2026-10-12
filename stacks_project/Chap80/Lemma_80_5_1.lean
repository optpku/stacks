/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap80.Definition_80_3_1_RelativelyRepresentable

/-!
# Representability of the diagonal of a presheaf by algebraic spaces

The diagonal of a presheaf on schemes over `S` is representable by algebraic
spaces if and only if every map from a scheme, equivalently from an algebraic
space, into that presheaf is representable by algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 80.5.1 (1): let `S` be a scheme. If `F` is a presheaf on `(Sch/S)_fppf`,
the diagonal `Δ_F : F ⟶ F ⨯ F` is representable by algebraic spaces if and only
if every map from a scheme `T` over `S` to `F` is representable by algebraic
spaces. -/
@[stacks 03Y2]
theorem representableByAlgebraicSpaces.diag_iff {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} :
    representableByAlgebraicSpaces (diag F) ↔
      ∀ ⦃T : Over S⦄ (a : yoneda.obj T ⟶ F), representableByAlgebraicSpaces a :=
  sorry

/-- Lemma 80.5.1 (2): let `S` be a scheme. If `F` is a presheaf on `(Sch/S)_fppf`,
the diagonal `Δ_F : F ⟶ F ⨯ F` is representable by algebraic spaces if and only
if every map from an algebraic space `X` over `S` to `F` is representable by
algebraic spaces. -/
@[stacks 03Y2]
theorem representableByAlgebraicSpaces.diag_iff_isAlgebraicSpace {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} :
    representableByAlgebraicSpaces (diag F) ↔
      ∀ ⦃X : (Over S)ᵒᵖ ⥤ Type u⦄ [IsAlgebraicSpace X] (a : X ⟶ F),
        representableByAlgebraicSpaces a :=
  sorry

/-- If the diagonal of a presheaf is representable by algebraic spaces, then every
map from a scheme over `S` to that presheaf is representable by algebraic
spaces. -/
theorem representableByAlgebraicSpaces.of_diag {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} (h : representableByAlgebraicSpaces (diag F))
    ⦃T : Over S⦄ (a : yoneda.obj T ⟶ F) :
    representableByAlgebraicSpaces a :=
  sorry

/-- If the diagonal of a presheaf is representable by algebraic spaces, then every
map from an algebraic space over `S` to that presheaf is representable by
algebraic spaces. -/
theorem representableByAlgebraicSpaces.of_diag_isAlgebraicSpace {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} (h : representableByAlgebraicSpaces (diag F))
    ⦃X : (Over S)ᵒᵖ ⥤ Type u⦄ [IsAlgebraicSpace X] (a : X ⟶ F) :
    representableByAlgebraicSpaces a :=
  sorry

/-- If every map from a scheme over `S` to a presheaf is representable by
algebraic spaces, then the diagonal of that presheaf is representable by
algebraic spaces. -/
theorem representableByAlgebraicSpaces.diag_of_yoneda {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u}
    (h : ∀ ⦃T : Over S⦄ (a : yoneda.obj T ⟶ F), representableByAlgebraicSpaces a) :
    representableByAlgebraicSpaces (diag F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
