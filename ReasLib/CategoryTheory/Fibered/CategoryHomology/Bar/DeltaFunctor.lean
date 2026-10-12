/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryHomology.Bar.Complex
public import ReasLib.CategoryTheory.Fibered.CategoryHomology
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Projection
public import ReasLib.CategoryTheory.Homology.HomologicalDeltaFunctor.Coeffaceable
public import ReasLib.CategoryTheory.Homology.HomologicalDeltaFunctor.ExactComplex
public import ReasLib.CategoryTheory.Homology.HomologicalDeltaFunctor.Universal
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fiber bar homology as a delta functor

The chain-level fiber Bar construction is sheafified degreewise on the base site.  Its homology
therefore carries a canonical homological delta-functor structure, independent of projective
resolutions or a chosen derived-category model.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v wX vX w

namespace CategoryTheory.FiberedCategoryOver.FiberHomology.Bar

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (X : FiberedCategoryOver.{u, v, wX, vX} C)
variable [UnivLE.{max wX vX, w}]
variable [HasSheafify J AddCommGrpCat.{w}]
variable [HasSheafify (X.p.inheritedTopology J) AddCommGrpCat.{w}]

/-- The fiber Bar complex on source sheaves, sheafified degreewise on the base. -/
@[stacks 08PJ "sheafified fiber bar complex functor"]
noncomputable abbrev sheafComplexFunctor :
    Sheaf (X.p.inheritedTopology J) AddCommGrpCat.{w} ⥤
      ChainComplex (Sheaf J AddCommGrpCat.{w}) ℕ :=
  sheafToPresheaf (X.p.inheritedTopology J) AddCommGrpCat.{w} ⋙
    complexFunctor X ⋙
      (presheafToSheaf J AddCommGrpCat.{w}).mapHomologicalComplex
        (ComplexShape.down ℕ)

/-- The sheafified fiber Bar complex is additive in the source sheaf. -/
@[stacks 08PJ "additivity of the sheafified fiber bar complex"]
instance sheafComplexFunctor.additive : (sheafComplexFunctor J X).Additive := sorry

/-- The sheafified fiber Bar complex preserves finite limits. -/
@[stacks 08PJ "finite-limit preservation of the sheafified fiber bar complex"]
instance sheafComplexFunctor.preservesFiniteLimits :
    PreservesFiniteLimits (sheafComplexFunctor J X) := sorry

/-- The sheafified fiber Bar complex preserves finite colimits. -/
@[stacks 08PJ "finite-colimit preservation of the sheafified fiber bar complex"]
instance sheafComplexFunctor.preservesFiniteColimits :
    PreservesFiniteColimits (sheafComplexFunctor J X) := sorry

/-- Exactness of the sheafified fiber Bar complex in the source sheaf. -/
@[stacks 08PJ "exactness of the sheafified fiber bar complex"]
theorem sheafComplexFunctor_exact :
    exactFunctor (Sheaf (X.p.inheritedTopology J) AddCommGrpCat.{w})
      (ChainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)
      (sheafComplexFunctor J X) := sorry

/-- The sheafified fiber Bar complex bundled with its exactness property. -/
@[stacks 08PJ "bundled exact sheafified fiber Bar complex"]
noncomputable def sheafComplexExactFunctor :
    Sheaf (X.p.inheritedTopology J) AddCommGrpCat.{w} ⥤ₑ
      ChainComplex (Sheaf J AddCommGrpCat.{w}) ℕ :=
  ⟨sheafComplexFunctor J X, sheafComplexFunctor_exact J X⟩

/-- The canonical homological delta functor of sheafified fiber Bar homology. -/
@[stacks 08PJ "fiber bar homological delta functor"]
noncomputable def deltaFunctor :
    HomologicalDeltaFunctor
      (Sheaf (X.p.inheritedTopology J) AddCommGrpCat.{w})
      (Sheaf J AddCommGrpCat.{w}) :=
  HomologicalDeltaFunctor.ExactComplex.functorBundled (sheafComplexExactFunctor J X)

/-- The degree branches of the fiber Bar delta functor are homology of the sheafified complex. -/
@[simp, stacks 08PJ "fiber bar delta functor degree formula"]
theorem deltaFunctor_obj (n : ℕ) :
    ((deltaFunctor J X n).obj) =
      sheafComplexFunctor J X ⋙
        HomologicalComplex.homologyFunctor
          (Sheaf J AddCommGrpCat.{w}) (ComplexShape.down ℕ) n := sorry

/-- Homology after degreewise sheafification agrees with sheafification of the fiberwise Bar
homology functor. -/
@[stacks 08PJ "fiber bar homology and sheafification comparison"]
theorem deltaFunctor_obj_isomorphic_sheafOfSheafFunctor (n : ℕ) :
    IsIsomorphic ((deltaFunctor J X n).obj) (sheafOfSheafFunctor J X n) := sorry

/-- Objectwise form of the fiber Bar homology and sheafification comparison. -/
@[stacks 08PJ "fiber bar homology and sheafification comparison on an object"]
theorem deltaFunctor_obj_obj_isomorphic_sheafOfSheaf
    (F : Sheaf (X.p.inheritedTopology J) AddCommGrpCat.{w}) (n : ℕ) :
    IsIsomorphic (((deltaFunctor J X n).obj).obj F) (sheafOfSheaf J X F n) := sorry

/-- The connecting morphism of the fiber Bar delta functor is the boundary of its sheafified
chain complex. -/
@[simp, stacks 08PJ "fiber bar delta functor connecting formula"]
theorem deltaFunctor_δ
    {S : ShortComplex (Sheaf (X.p.inheritedTopology J) AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n : ℕ) :
    (deltaFunctor J X).δ hS n =
      HomologicalDeltaFunctor.ExactComplex.connecting
        (sheafComplexExactFunctor J X).1 hS n := sorry

/-- Every positive degree of the fiber Bar delta functor is coeffaceable. -/
@[stacks 08PJ "coeffaceability of positive fiber bar homology"]
theorem deltaFunctor_degree_isCoeffaceable (n : ℕ) (hn : 0 < n) :
    ((deltaFunctor J X n).obj).IsCoeffaceable := sorry

/-- The fiber Bar homological delta functor is universal. -/
@[stacks 08PJ "universality of fiber bar homology"]
instance deltaFunctor.isUniversal :
    HomologicalDeltaFunctor.IsUniversal (deltaFunctor J X) := sorry

variable [
  (X.p.sheafPushforwardContinuous AddCommGrpCat.{w}
    (X.p.inheritedTopology J) J).IsRightAdjoint]

/-- Degree-zero fiber Bar homology is the lower shriek along the projection of the fibered
category.  This is the functorial, library-facing form of the fiberwise-colimit calculation. -/
@[stacks 08PJ "degree-zero fiber bar homology is lower shriek"]
theorem lowerShriek_isomorphic_deltaFunctor_zero :
    IsIsomorphic
      (X.p.sheafPullback AddCommGrpCat.{w} (X.p.inheritedTopology J) J)
      ((deltaFunctor J X 0).obj) := sorry

/-- Any universal homological delta functor extending projection lower shriek is degreewise
isomorphic to fiber Bar homology.  This is the resolution-independent comparison underlying
Lemma 21.40.2. -/
@[stacks 08PJ "universal derived lower shriek and fiber bar homology"]
theorem universal_degree_isomorphic
    (T : HomologicalDeltaFunctor
      (Sheaf (X.p.inheritedTopology J) AddCommGrpCat.{w})
      (Sheaf J AddCommGrpCat.{w}))
    [T.IsUniversal]
    (h₀ : IsIsomorphic (T 0).obj
      (X.p.sheafPullback AddCommGrpCat.{w} (X.p.inheritedTopology J) J))
    (n : ℕ) :
    IsIsomorphic (T n).obj (sheafOfSheafFunctor J X n) := sorry

/-- Objectwise readout of the universal comparison with fiber Bar homology. -/
@[stacks 08PJ "universal derived lower shriek and fiber bar homology on an object"]
theorem universal_obj_isomorphic
    (T : HomologicalDeltaFunctor
      (Sheaf (X.p.inheritedTopology J) AddCommGrpCat.{w})
      (Sheaf J AddCommGrpCat.{w}))
    [T.IsUniversal]
    (h₀ : IsIsomorphic (T 0).obj
      (X.p.sheafPullback AddCommGrpCat.{w} (X.p.inheritedTopology J) J))
    (F : Sheaf (X.p.inheritedTopology J) AddCommGrpCat.{w}) (n : ℕ) :
    IsIsomorphic ((T n).obj.obj F) (sheafOfSheaf J X F n) := sorry

end CategoryTheory.FiberedCategoryOver.FiberHomology.Bar
