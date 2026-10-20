module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeOver

/-!
# Closed immersions and finite presentation on schemes over an algebraic space

Relative representability of morphisms of `Type (u + 1)` functors on `SchemeOver B`
with respect to `uliftYoneda`, with represented pullbacks required to be closed
immersions or morphisms of finite presentation of schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SchemeOver

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- A morphism of `Type (u + 1)` functors on schemes over `B` is a closed
immersion when it is relatively representable with respect to `uliftYoneda` and
every represented pullback is a closed immersion of schemes. -/
def IsClosedImmersion {F G : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)}
    (φ : F ⟶ G) : Prop :=
  let P : MorphismProperty (SchemeOver B) :=
    fun _ _ h ↦ AlgebraicGeometry.IsClosedImmersion h.left.left
  P.relative uliftYoneda.{u + 1} φ

/-- Closed immersions of `Type (u + 1)` functors are relatively representable
`uliftYoneda` morphisms whose represented scheme maps are closed immersions. -/
theorem isClosedImmersion_iff {F G : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)}
    (φ : F ⟶ G) :
    IsClosedImmersion φ ↔
      uliftYoneda.{u + 1}.relativelyRepresentable φ ∧
        ∀ ⦃σ τ : SchemeOver B⦄ (ξ : uliftYoneda.{u + 1}.obj σ ⟶ G)
          (fst : uliftYoneda.{u + 1}.obj τ ⟶ F) (snd : τ ⟶ σ),
          IsPullback fst (uliftYoneda.{u + 1}.map snd) φ ξ →
            AlgebraicGeometry.IsClosedImmersion snd.left.left := sorry

/-- A morphism of `Type (u + 1)` functors on schemes over `B` is of finite
presentation when it is relatively representable with respect to `uliftYoneda`
and every represented pullback is locally of finite presentation, quasi-compact,
and quasi-separated as a morphism of schemes. -/
def IsFinitePresentation {F G : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)}
    (φ : F ⟶ G) : Prop :=
  let P : MorphismProperty (SchemeOver B) :=
    fun _ _ h ↦
      AlgebraicGeometry.LocallyOfFinitePresentation h.left.left ∧
        AlgebraicGeometry.QuasiCompact h.left.left ∧
        AlgebraicGeometry.QuasiSeparated h.left.left
  P.relative uliftYoneda.{u + 1} φ

/-- Finite presentation of `Type (u + 1)` functors is relative representability for
`uliftYoneda` together with local finite presentation, quasi-compactness, and
quasi-separatedness of every represented scheme map. -/
theorem isFinitePresentation_iff
    {F G : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)} (φ : F ⟶ G) :
    IsFinitePresentation φ ↔
      uliftYoneda.{u + 1}.relativelyRepresentable φ ∧
        ∀ ⦃σ τ : SchemeOver B⦄ (ξ : uliftYoneda.{u + 1}.obj σ ⟶ G)
          (fst : uliftYoneda.{u + 1}.obj τ ⟶ F) (snd : τ ⟶ σ),
          IsPullback fst (uliftYoneda.{u + 1}.map snd) φ ξ →
            AlgebraicGeometry.LocallyOfFinitePresentation snd.left.left ∧
              AlgebraicGeometry.QuasiCompact snd.left.left ∧
              AlgebraicGeometry.QuasiSeparated snd.left.left := sorry

end AlgebraicGeometry.AlgebraicSpace.SchemeOver
