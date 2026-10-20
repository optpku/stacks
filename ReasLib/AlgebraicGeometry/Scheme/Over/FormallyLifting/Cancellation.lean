module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Over.FormallyLifting

/-!
# Cancellation of formally smooth, étale, and unramified transformations

If `b : G ⟶ H` is formally unramified, then formal unramifiedness, étaleness, or
smoothness of `a ≫ b` implies the same property of `a`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.Over

namespace FormallyUnramified

/-- Formal unramifiedness of a transformation of functors is cancellable on the
left against a formally unramified postcomposition. -/
instance instHasOfPostcompProperty {S : Scheme.{u}} :
    MorphismProperty.HasOfPostcompProperty
      (fun _ _ transformation ↦ FormallyUnramified transformation :
        MorphismProperty ((Over S)ᵒᵖ ⥤ Type v))
      (fun _ _ transformation ↦ FormallyUnramified transformation :
        MorphismProperty ((Over S)ᵒᵖ ⥤ Type v)) := sorry

/-- If `b` is formally unramified and `a ≫ b` is formally unramified, then `a`
is formally unramified. -/
theorem of_comp {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) (b : G ⟶ H) [FormallyUnramified b] [FormallyUnramified (a ≫ b)] :
    FormallyUnramified a := sorry

end FormallyUnramified

namespace FormallyEtale

/-- Formal étaleness of a transformation of functors is cancellable on the left
against a formally unramified postcomposition. -/
instance instHasOfPostcompProperty {S : Scheme.{u}} :
    MorphismProperty.HasOfPostcompProperty
      (fun _ _ transformation ↦ FormallyEtale transformation :
        MorphismProperty ((Over S)ᵒᵖ ⥤ Type v))
      (fun _ _ transformation ↦ FormallyUnramified transformation :
        MorphismProperty ((Over S)ᵒᵖ ⥤ Type v)) := sorry

/-- If `b` is formally unramified and `a ≫ b` is formally étale, then `a` is
formally étale. -/
theorem of_comp {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) (b : G ⟶ H) [FormallyUnramified b] [FormallyEtale (a ≫ b)] :
    FormallyEtale a := sorry

end FormallyEtale

namespace FormallySmooth

/-- Formal smoothness of a transformation of functors is cancellable on the left
against a formally unramified postcomposition. -/
instance instHasOfPostcompProperty {S : Scheme.{u}} :
    MorphismProperty.HasOfPostcompProperty
      (fun _ _ transformation ↦ FormallySmooth transformation :
        MorphismProperty ((Over S)ᵒᵖ ⥤ Type v))
      (fun _ _ transformation ↦ FormallyUnramified transformation :
        MorphismProperty ((Over S)ᵒᵖ ⥤ Type v)) := sorry

/-- If `b` is formally unramified and `a ≫ b` is formally smooth, then `a` is
formally smooth. -/
theorem of_comp {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) (b : G ⟶ H) [FormallyUnramified b] [FormallySmooth (a ≫ b)] :
    FormallySmooth a := sorry

end FormallySmooth

end AlgebraicGeometry.Scheme.Over
