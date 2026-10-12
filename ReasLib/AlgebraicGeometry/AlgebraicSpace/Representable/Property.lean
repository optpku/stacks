/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Pullback

/-!
# Relative morphism properties for maps representable by algebraic spaces

A morphism property of algebraic spaces over `S` transfers to morphisms of
presheaves representable by algebraic spaces by testing the structure morphisms
of scheme Yoneda pullbacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace representableByAlgebraicSpaces

/-- A morphism of presheaves representable by algebraic spaces has a morphism
property `P` of algebraic spaces when every scheme Yoneda pullback
`U ×_G F ⟶ U` has property `P`. -/
def has {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    (ha : representableByAlgebraicSpaces a)
    (P : MorphismProperty (AlgebraicSpace S)) : Prop :=
  ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ G), P (ha.pullbackHom ξ)

/-- A representable-by-algebraic-spaces morphism has property `P` if and only if
every scheme Yoneda pullback has property `P`. -/
theorem has_iff {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    (ha : representableByAlgebraicSpaces a)
    (P : MorphismProperty (AlgebraicSpace S)) :
    ha.has P ↔ ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ G), P (ha.pullbackHom ξ) :=
  sorry

end representableByAlgebraicSpaces

/-- Transfer of a morphism property `P` of algebraic spaces over `S` to morphisms
of presheaves on `(Over S)ᵒᵖ`. A morphism `a : F ⟶ G` satisfies
`relativeAlgebraicSpaces P` when it is representable by algebraic spaces and
every scheme Yoneda pullback `U ×_G F ⟶ U` has property `P`.

The definition applies to arbitrary morphism properties; stability under base
change and fppf locality on the target are not assumptions of the definition. -/
def relativeAlgebraicSpaces {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) :
    MorphismProperty ((Over S)ᵒᵖ ⥤ Type u) :=
  fun _ _ a ↦ representableByAlgebraicSpaces a ∧
    ∀ (ha : representableByAlgebraicSpaces a), ha.has P

/-- A morphism of presheaves has the transferred property `P` if and only if it is
representable by algebraic spaces and every scheme Yoneda pullback has property
`P`. -/
theorem relativeAlgebraicSpaces_iff {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    (P : MorphismProperty (AlgebraicSpace S)) :
    relativeAlgebraicSpaces P a ↔
      representableByAlgebraicSpaces a ∧
        ∀ (ha : representableByAlgebraicSpaces a) ⦃U : Over S⦄
          (ξ : yoneda.obj U ⟶ G), P (ha.pullbackHom ξ) :=
  sorry

namespace relativeAlgebraicSpaces

/-- A morphism representable by algebraic spaces whose scheme Yoneda pullbacks
have property `P` satisfies `relativeAlgebraicSpaces P`. -/
theorem of {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    (P : MorphismProperty (AlgebraicSpace S))
    (ha : representableByAlgebraicSpaces a)
    (hP : ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ G), P (ha.pullbackHom ξ)) :
    relativeAlgebraicSpaces P a :=
  sorry

/-- A morphism satisfying `relativeAlgebraicSpaces P` is representable by
algebraic spaces. -/
theorem representable {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    {P : MorphismProperty (AlgebraicSpace S)} (h : relativeAlgebraicSpaces P a) :
    representableByAlgebraicSpaces a :=
  sorry

/-- Scheme Yoneda pullbacks of a morphism satisfying `relativeAlgebraicSpaces P`
have property `P`. -/
theorem property_pullbackHom {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    {P : MorphismProperty (AlgebraicSpace S)} (h : relativeAlgebraicSpaces P a)
    ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ G) :
    P ((representable h).pullbackHom ξ) :=
  sorry

end relativeAlgebraicSpaces

end AlgebraicGeometry.AlgebraicSpace
