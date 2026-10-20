module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Descent of syntomic morphisms of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Syntomic

/-- In a commutative triangle `f ≫ q = p` of algebraic spaces over `S`,
syntomicity descends from `p` to `q` along a surjective syntomic morphism `f`. -/
theorem of_comp_eq_of_surjective {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (f : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    [Surjective f] [Syntomic f] [Syntomic p] (hcomm : f ≫ q = p) :
    Syntomic q := sorry

/-- Syntomicity of morphisms of algebraic spaces descends under precomposition by
surjective syntomic morphisms. -/
instance hasOfPrecompSurjective {S : Scheme.{u}} :
    MorphismProperty.HasOfPrecompProperty
      (@Syntomic S : MorphismProperty (AlgebraicSpace S))
      ((@Surjective S ⊓ @Syntomic S) : MorphismProperty (AlgebraicSpace S)) where
  of_precomp {X Y Z} f g hf hfg :=
    @of_comp_eq_of_surjective S X Y Z f (f ≫ g) g hf.1 hf.2 hfg rfl

/-- Syntomicity of morphisms of algebraic spaces descends under precomposition by
surjective, flat, locally of finite presentation morphisms. -/
instance hasOfPrecompFppf {S : Scheme.{u}} :
    MorphismProperty.HasOfPrecompProperty
      (@Syntomic S : MorphismProperty (AlgebraicSpace S))
      ((@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S) :
        MorphismProperty (AlgebraicSpace S)) := sorry

/-- In a commutative triangle `f ≫ q = p` of algebraic spaces over `S`,
syntomicity descends from `p` to `q` when `f` is surjective, flat, and locally of
finite presentation. -/
theorem of_comp_eq_of_fppf {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (f : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f] [Syntomic p]
    (hcomm : f ≫ q = p) : Syntomic q := sorry

/-- If `f` is a surjective, flat, and locally of finite presentation morphism of
algebraic spaces over `S` and `f ≫ q` is syntomic, then `f` is syntomic. -/
theorem left_of_comp_of_fppf {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ B)
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f]
    (hcomp : Syntomic (f ≫ q)) : Syntomic f := sorry

end AlgebraicGeometry.AlgebraicSpace.Syntomic
