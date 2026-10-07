module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite
public import stacks_project.Chap80.Lemma_80_4_6

/-!
# Locally quasi-finite morphisms representable by algebraic spaces

A morphism from a scheme over `S` to a functor on `(Over S)ᵒᵖ` that is
representable by algebraic spaces and locally quasi-finite is representable
by schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 80.5.4: let `S` be a scheme. Let `F : (Over S)ᵒᵖ ⥤ Type u` be a
functor. Let `X` be a scheme over `S` and let `a : yoneda.obj X ⟶ F` be
representable by algebraic spaces, with base changes along Yoneda sections
locally of finite type and locally quasi-finite as morphisms of algebraic
spaces. Then `a` is representable by schemes, in the sense of
`yoneda.relativelyRepresentable`. -/
@[stacks 0AHV]
theorem relativelyRepresentable_of_locallyQuasiFinite
    {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u} {X : Over S}
    (a : yoneda.obj X ⟶ F) (ha : representableByAlgebraicSpaces a)
    (h_locallyOfFiniteType :
      ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ F), LocallyOfFiniteType (ha.pullbackHom ξ))
    (h_locallyQuasiFinite :
      ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ F), LocallyQuasiFinite (ha.pullbackHom ξ)) :
    yoneda.relativelyRepresentable a :=
  sorry

namespace representableByAlgebraicSpaces

/-- The fibre product algebraic space of a locally quasi-finite morphism
representable by algebraic spaces along a Yoneda section is a scheme. -/
theorem isScheme_pullbackSpace {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {X : Over S} (a : yoneda.obj X ⟶ F) (ha : representableByAlgebraicSpaces a)
    (h_locallyOfFiniteType :
      ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ F), LocallyOfFiniteType (ha.pullbackHom ξ))
    (h_locallyQuasiFinite :
      ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ F), LocallyQuasiFinite (ha.pullbackHom ξ))
    ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ F) :
    IsScheme (ha.pullbackSpace ξ) :=
  sorry

/-- Each Yoneda pullback of a locally quasi-finite morphism representable by
algebraic spaces is a representable functor. -/
theorem isRepresentable_pullback {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {X : Over S} (a : yoneda.obj X ⟶ F) (ha : representableByAlgebraicSpaces a)
    (h_locallyOfFiniteType :
      ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ F), LocallyOfFiniteType (ha.pullbackHom ξ))
    (h_locallyQuasiFinite :
      ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ F), LocallyQuasiFinite (ha.pullbackHom ξ))
    ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ F) :
    (pullback ξ a).IsRepresentable :=
  sorry

end representableByAlgebraicSpaces

end AlgebraicGeometry.AlgebraicSpace
