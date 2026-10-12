/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable

/-!
# Morphisms of presheaves representable by algebraic spaces

A morphism of presheaves on schemes over `S` is representable by algebraic spaces when
every base change along a Yoneda section from a scheme over `S` is an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (@representableByAlgebraicSpaces :
  ∀ {S : Scheme.{u}}, MorphismProperty ((Over S)ᵒᵖ ⥤ Type u))

#check (representableByAlgebraicSpaces_iff :
  ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G),
    representableByAlgebraicSpaces a ↔
      ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ G), IsAlgebraicSpace (pullback ξ a))

#check (representableByAlgebraicSpaces.isAlgebraicSpace_pullback :
  ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    (ha : representableByAlgebraicSpaces a) {U : Over S} (ξ : yoneda.obj U ⟶ G),
    IsAlgebraicSpace (pullback ξ a))

#check (representableByAlgebraicSpaces.of_isAlgebraicSpace_pullback :
  ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G},
    (∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ G), IsAlgebraicSpace (pullback ξ a)) →
      representableByAlgebraicSpaces a)

#check (representableByAlgebraicSpaces.exists_algebraicSpace :
  ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    (ha : representableByAlgebraicSpaces a) {U : Over S} (ξ : yoneda.obj U ⟶ G),
    ∃ X : AlgebraicSpace S, X.functorOfPoints = pullback ξ a)

end AlgebraicGeometry.AlgebraicSpace
