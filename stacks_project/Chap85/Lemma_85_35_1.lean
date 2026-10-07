module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.ComposableArrows.Three
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import stacks_project.Chap85.Lemma_85_35_1_HomSequence

/-!
# Lemma 85.35.1

Negative Ext-groups of quasi-coherent complexes on an algebraic space vanish
as soon as they vanish after derived pullback along every stage of an fppf
hypercovering, and the Čech Hom sequence in degrees `0` and `1` is exact.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Simplicial
open CategoryTheory.ComposableArrows Functor
open scoped DerivedExt Simplicial ZeroObject

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- Lemma 85.35.1 (1). Let `X` be an algebraic space over a scheme `S`. Let
`K`, `E` be objects of `DerivedQCoh X`. Let `a : U ⟶ X` be an fppf
hypercovering. If `Ext⁽i⁾((modulePullbackDerived (stageMap a n)).obj K.obj,
(modulePullbackDerived (stageMap a n)).obj E.obj)` is a subsingleton for all
`n : ℕ` and all `i < 0`, then `Ext⁽i⁾(K.obj, E.obj)` is a subsingleton for all
`i < 0`. -/
@[stacks 0DL9]
theorem negExt_eq_zero (ha : IsFppfHypercovering a)
    (K E : AlgebraicSpace.DerivedQCoh X)
    (h_ext : ∀ n : ℕ, ∀ i : ℤ, i < 0 →
      Subsingleton
        (Ext⁽i⁾((modulePullbackDerived (stageMap a n)).obj K.obj,
          (modulePullbackDerived (stageMap a n)).obj E.obj)))
    (i : ℤ) (hi : i < 0) :
    Subsingleton (Ext⁽i⁾(K.obj, E.obj)) :=
  sorry

/-- Lemma 85.35.1 (2). Let `X` be an algebraic space over a scheme `S`. Let
`K`, `E` be objects of `DerivedQCoh X`. Let `a : U ⟶ X` be an fppf
hypercovering. If `Ext⁽i⁾((modulePullbackDerived (stageMap a n)).obj K.obj,
(modulePullbackDerived (stageMap a n)).obj E.obj)` is a subsingleton for all
`n : ℕ` and all `i < 0`, then the sequence
`0 ⟶ Hom(K, E) ⟶ Hom(La_0^* K, La_0^* E) ⟶ Hom(La_1^* K, La_1^* E)`
given by `homRestrict a K E` and `homDiff a K E` is exact. -/
@[stacks 0DL9]
theorem homSequence_exact (ha : IsFppfHypercovering a)
    (K E : AlgebraicSpace.DerivedQCoh X)
    (h_ext : ∀ n : ℕ, ∀ i : ℤ, i < 0 →
      Subsingleton
        (Ext⁽i⁾((modulePullbackDerived (stageMap a n)).obj K.obj,
          (modulePullbackDerived (stageMap a n)).obj E.obj))) :
    (mk₃ (0 : 0 ⟶ AddCommGrpCat.of (K.obj ⟶ E.obj))
      (homRestrict a K E) (homDiff a K E)).Exact :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
