/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.EilenbergMacLane.Extension.Index
public import ReasLib.AlgebraicTopology.DoldKan.Gamma.DegreewiseSplit
public import ReasLib.CategoryTheory.ShortComplex.FunctorCategory
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
@stack 0192

# Short exact Eilenberg-MacLane extensions

This file owns the natural inclusion and projection of the Eilenberg-MacLane extension, their
functor-category short complex, and its pointwise degree splitting. The summand decomposition is
an independent downstream leaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomologicalComplex
open scoped Simplicial DoldKan

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.eilenbergMacLane.extension

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] [HasZeroObject 𝒜]
variable [HasFiniteCoproducts 𝒜]

/-- The inclusions `K(A, k) ⟶ object A k` are natural in `A`. -/
@[stacks 0192 "Eilenberg-MacLane extension inclusion"]
noncomputable def inclusion (k : ℕ) :
    eilenbergMacLane.functor (A := 𝒜) k ⟶
      extension.functor (𝒜 := 𝒜) k :=
  Functor.whiskerRight (ChainComplex.disk.ι 𝒜 k)
    AlgebraicTopology.DoldKan.Γ₀

/-- The projections `object A k ⟶ K(A, k + 1)` are natural in `A`. -/
@[stacks 0192 "Eilenberg-MacLane extension projection"]
noncomputable def projection (k : ℕ) :
    extension.functor (𝒜 := 𝒜) k ⟶
      eilenbergMacLane.functor (A := 𝒜) (k + 1) :=
  Functor.whiskerRight (ChainComplex.disk.π 𝒜 k)
    AlgebraicTopology.DoldKan.Γ₀

/-- The coefficient component of the simplicial inclusion is obtained by applying `Γ₀` to the
chain-level inclusion component. -/
@[simp, stacks 0192 "pointwise Eilenberg-MacLane extension inclusion"]
theorem inclusion_app (A : 𝒜) (k : ℕ) :
    (inclusion (𝒜 := 𝒜) k).app A =
      AlgebraicTopology.DoldKan.Γ₀.map (ChainComplex.disk.ιApp A k) := sorry

/-- The coefficient component of the simplicial projection is obtained by applying `Γ₀` to the
chain-level projection component. -/
@[simp, stacks 0192 "pointwise Eilenberg-MacLane extension projection"]
theorem projection_app (A : 𝒜) (k : ℕ) :
    (projection (𝒜 := 𝒜) k).app A =
      AlgebraicTopology.DoldKan.Γ₀.map (ChainComplex.disk.πApp A k) := sorry

/-- The natural maps in the Eilenberg-MacLane extension compose to zero. -/
@[stacks 0192 "Eilenberg-MacLane extension composition"]
theorem comp (k : ℕ) : inclusion (𝒜 := 𝒜) k ≫ projection k = 0 := sorry

/-- The short complex obtained by applying the explicit inverse Dold-Kan functor to the
chain-level inclusion and projection. -/
@[stacks 0192 "functorial Eilenberg-MacLane extension short complex"]
noncomputable def shortComplex (k : ℕ) : ShortComplex (𝒜 ⥤ SimplicialObject 𝒜) :=
  (ChainComplex.disk.shortComplex 𝒜 k).map
    ((Functor.whiskeringRight 𝒜 (ChainComplex 𝒜 ℕ)
      (SimplicialObject 𝒜)).obj AlgebraicTopology.DoldKan.Γ₀)

namespace shortComplex

/-- Evaluation of the functor-category short complex gives a functorial family of extensions. -/
@[stacks 0192 "Eilenberg-MacLane extension functor"]
noncomputable abbrev functor (k : ℕ) : 𝒜 ⥤ ShortComplex (SimplicialObject 𝒜) :=
  (ShortComplex.FunctorEquivalence.functor 𝒜 (SimplicialObject 𝒜)).obj
    (extension.shortComplex k)

/-- The Eilenberg-MacLane extension short complex
`K(A, k) ⟶ object A k ⟶ K(A, k + 1)`. -/
@[stacks 0192 "Eilenberg-MacLane extension short complex"]
noncomputable abbrev app (A : 𝒜) (k : ℕ) :
    ShortComplex (SimplicialObject 𝒜) :=
  ShortComplex.FunctorCategory.app (extension.shortComplex k) A

/-- The first map in the objectwise extension is the component of the natural inclusion. -/
@[simp, stacks 0192 "objectwise Eilenberg-MacLane extension inclusion"]
theorem app.f (A : 𝒜) (k : ℕ) :
    (app A k).f = (inclusion k).app A := sorry

/-- The second map in the objectwise extension is the component of the natural projection. -/
@[simp, stacks 0192 "objectwise Eilenberg-MacLane extension projection"]
theorem app.g (A : 𝒜) (k : ℕ) :
    (app A k).g = (projection k).app A := sorry

end shortComplex

namespace degree

/-- The pointwise splitting of the Eilenberg-MacLane extension is the canonical `Γ₀` image of
the chosen degreewise splitting of the disk row. -/
@[stacks 0192 "termwise split Eilenberg-MacLane extension"]
noncomputable abbrev splitting (A : 𝒜) (k : ℕ) :
    ShortComplex.FunctorCategory.PointwiseSplitting
      (shortComplex.app A k) :=
  (ChainComplex.disk.degreewiseSplitting A k).mapΓ₀

end degree

/-- The Eilenberg-MacLane extension is short exact in the functor category. -/
@[stacks 0192 "functorial short exact Eilenberg-MacLane extension"]
theorem shortComplex.shortExact (k : ℕ) :
    (shortComplex (𝒜 := 𝒜) k).ShortExact := sorry

/-- Every objectwise Eilenberg-MacLane extension is short exact. -/
@[stacks 0192 "short exact Eilenberg-MacLane extension"]
theorem shortComplex.app.shortExact (A : 𝒜) (k : ℕ) :
    (shortComplex.app A k).ShortExact := sorry

end CategoryTheory.SimplicialObject.eilenbergMacLane.extension
