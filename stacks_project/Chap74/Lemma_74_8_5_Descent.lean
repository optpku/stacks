/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap67.Lemma_67_36_4_Syntomic

/-!
# Descent of syntomicity along fppf morphisms

If `f` is a surjective, flat, and locally of finite presentation morphism of
algebraic spaces, and `f ≫ q` is syntomic, then both `q` and `f` are syntomic.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Syntomic

/-- Syntomicity of morphisms of algebraic spaces descends under precomposition by
a surjective, flat, locally of finite presentation morphism. -/
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

end Syntomic

end AlgebraicGeometry.AlgebraicSpace
