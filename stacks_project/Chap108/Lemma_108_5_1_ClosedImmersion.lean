module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeOver.MorphismProperty
public import stacks_project.Chap99.«99_8_1_1_Functor»

/-!
# Closed immersions and finite presentation on schemes over an algebraic space

Relative representability of morphisms of `Type (u + 1)` functors on `SchemesOver B`
with respect to `uliftYoneda`, with represented pullbacks required to be closed
immersions or morphisms of finite presentation of schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- A closed immersion of presheaves on schemes over `B`, using the shared
scheme-representable morphism predicate. -/
abbrev IsClosedImmersionOnSchemesOver {F G : (SchemesOver B)ᵒᵖ ⥤ Type (u + 1)}
    (φ : F ⟶ G) : Prop :=
  SchemeOver.IsClosedImmersion φ

/-- A finitely presented morphism of presheaves on schemes over `B`, using the
shared scheme-representable morphism predicate. -/
abbrev IsFinitePresentationOnSchemesOver {F G : (SchemesOver B)ᵒᵖ ⥤ Type (u + 1)}
    (φ : F ⟶ G) : Prop :=
  SchemeOver.IsFinitePresentation φ

#check (AlgebraicGeometry.AlgebraicSpace.SchemeOver.isClosedImmersion_iff :
  ∀ {F G : (SchemesOver B)ᵒᵖ ⥤ Type (u + 1)} (φ : F ⟶ G),
    IsClosedImmersionOnSchemesOver φ ↔
      uliftYoneda.{u + 1}.relativelyRepresentable φ ∧
        ∀ ⦃σ τ : SchemesOver B⦄ (ξ : uliftYoneda.{u + 1}.obj σ ⟶ G)
          (fst : uliftYoneda.{u + 1}.obj τ ⟶ F) (snd : τ ⟶ σ),
          IsPullback fst (uliftYoneda.{u + 1}.map snd) φ ξ →
            AlgebraicGeometry.IsClosedImmersion snd.left.left)

#check (AlgebraicGeometry.AlgebraicSpace.SchemeOver.isFinitePresentation_iff :
  ∀ {F G : (SchemesOver B)ᵒᵖ ⥤ Type (u + 1)} (φ : F ⟶ G),
    IsFinitePresentationOnSchemesOver φ ↔
      uliftYoneda.{u + 1}.relativelyRepresentable φ ∧
        ∀ ⦃σ τ : SchemesOver B⦄ (ξ : uliftYoneda.{u + 1}.obj σ ⟶ G)
          (fst : uliftYoneda.{u + 1}.obj τ ⟶ F) (snd : τ ⟶ σ),
          IsPullback fst (uliftYoneda.{u + 1}.map snd) φ ξ →
            AlgebraicGeometry.LocallyOfFinitePresentation snd.left.left ∧
              AlgebraicGeometry.QuasiCompact snd.left.left ∧
              AlgebraicGeometry.QuasiSeparated snd.left.left)

end AlgebraicGeometry.AlgebraicSpace.Quot
