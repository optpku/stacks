module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Descent
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Descent of syntomic morphisms

This file records descent of syntomicity along surjective syntomic morphisms and
surjective, flat, locally finitely presented morphisms of schemes.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Syntomic

/-- If `f` is a surjective syntomic morphism, `f ≫ q` is syntomic, and `q` is locally of
finite presentation, then `q` is syntomic. -/
theorem of_comp_surjective {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S)
    [Surjective f] (hf : Syntomic f) (hfq : Syntomic (f ≫ q))
    (hq : LocallyOfFinitePresentation q) : Syntomic q := sorry

/-- In a commutative triangle `f ≫ q = p`, syntomicity descends from `p` to `q`
along a surjective syntomic morphism `f`. -/
theorem of_comp_eq_of_surjective {X Y S : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ S)
    (q : Y ⟶ S) [Surjective f] [Syntomic f] [Syntomic p] (hcomm : f ≫ q = p) :
    Syntomic q := sorry

/-- If `f` is surjective, flat, and locally of finite presentation and `f ≫ q` is
syntomic, then `f` is syntomic. -/
theorem left_of_comp_of_fppf {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S)
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f]
    (hcomp : Syntomic (f ≫ q)) : Syntomic f := sorry

/-- Syntomicity descends under precomposition by a surjective, flat, locally finitely
presented morphism. -/
instance hasOfPrecompFppf :
    MorphismProperty.HasOfPrecompProperty
      (@Syntomic : MorphismProperty Scheme.{u})
      ((@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :
        MorphismProperty Scheme.{u}) := sorry

end AlgebraicGeometry.Syntomic
