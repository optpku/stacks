module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap80.Lemma_80_4_6

/-!
# Closed immersions of formal algebraic spaces

A morphism of functors of points on schemes over `S` is a closed immersion
when it is representable by algebraic spaces and every Yoneda pullback is a
closed immersion of algebraic spaces, in the sense of Bootstrap, Definition
03XZ.

This owner reuses the canonical representable Yoneda pullback constructor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- A morphism of functors of points on schemes over `S` is a closed
immersion when it is representable by algebraic spaces and every Yoneda
pullback is a closed immersion of algebraic spaces. -/
@[mk_iff]
class ClosedImmersion {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    Prop where
  /-- `f` is representable by algebraic spaces. -/
  representable : representableByAlgebraicSpaces f
  /-- Every Yoneda pullback of `f` is a closed immersion of algebraic spaces. -/
  of_pullback :
    ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
      AlgebraicSpace.IsClosedImmersion (representableByAlgebraicSpaces.pullbackHom representable ξ)

namespace ClosedImmersion

/-- A morphism of functors of points is a closed immersion if and only if it is
representable by algebraic spaces and every Yoneda pullback is a closed
immersion of algebraic spaces. -/
theorem iff {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    ClosedImmersion f ↔
      ∃ (h : representableByAlgebraicSpaces f),
        ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
          AlgebraicSpace.IsClosedImmersion (representableByAlgebraicSpaces.pullbackHom h ξ) :=
  sorry

/-- The identity morphism of a functor of points is a closed immersion. -/
instance id {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} : ClosedImmersion (𝟙 X) :=
  sorry

/-- A closed immersion is representable by algebraic spaces. -/
theorem relativelyRepresentable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) [ClosedImmersion f] : representableByAlgebraicSpaces f :=
  sorry

/-- Yoneda pullbacks of a closed immersion are closed immersions of algebraic
spaces. -/
theorem spec {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    [hf : ClosedImmersion f] {U : Over S} (ξ : yoneda.obj U ⟶ Y) :
    representableByAlgebraicSpaces f ∧
      AlgebraicSpace.IsClosedImmersion (representableByAlgebraicSpaces.pullbackHom hf.representable ξ) :=
  sorry

end ClosedImmersion

end AlgebraicGeometry.FormalAlgebraicSpace
