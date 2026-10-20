module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Descent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Descent

/-!
# Descent of étale morphisms

This file records descent of étaleness along surjective étale morphisms of schemes and under
fppf precomposition.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Etale

/-- Étaleness descends under precomposition by a surjective, flat, locally finitely
presented morphism. -/
instance hasOfPrecompFppf :
    MorphismProperty.HasOfPrecompProperty
      (@Etale : MorphismProperty Scheme.{u})
      ((@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :
        MorphismProperty Scheme.{u}) := sorry

/-- In a commutative triangle `f ≫ q = p`, étaleness descends from `p` to `q` when `f` is
surjective, flat, and locally of finite presentation. -/
theorem of_comp_eq_of_fppf {X Y S : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ S)
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f] [Etale p]
    (hcomm : f ≫ q = p) : Etale q := sorry

/-- If `f` is a surjective étale morphism, `f ≫ q` is étale, and `q` is locally of finite
presentation, then `q` is étale. -/
theorem of_comp_surjective {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S)
    [Surjective f] (hf : Etale f) (hfq : Etale (f ≫ q))
    (hq : LocallyOfFinitePresentation q) : Etale q := sorry

/-- In a commutative triangle `f ≫ q = p`, étaleness descends from `p` to `q`
along a surjective étale morphism `f`. -/
theorem of_comp_eq_of_surjective {X Y S : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ S)
    (q : Y ⟶ S) [Surjective f] [Etale f] [Etale p] (hcomm : f ≫ q = p) :
    Etale q := sorry

end AlgebraicGeometry.Etale
