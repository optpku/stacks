/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Tactic.CrossRefAttribute

/-!
# Linear homology in derived categories

The canonical homology functors of an `R`-linear abelian category are
`R`-linear.  The scalar-multiplication triangle API records the reusable
long-exact-sequence consequence needed by localization arguments.
@stack 0H84
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

noncomputable section

universe t w v u

namespace CategoryTheory.DerivedCategory

variable {R : Type t} [Ring R]
variable {C : Type u} [Category.{v} C] [Abelian C]
variable [CategoryTheory.Linear R C] [HasDerivedCategory.{w} C]

/-- Homology of derived objects is linear over every scalar ring acting linearly
on the underlying abelian category. -/
@[stacks 0H84 "derived homology functor is linear"]
instance homologyFunctor_linear (i : ℤ) :
    Functor.Linear R (DerivedCategory.homologyFunctor C i) := sorry

namespace SmulTriangle

/-- In a triangle whose first map is multiplication by `r`, a lower bound on
the cone makes multiplication by `r` monic on homology below the next degree. -/
@[stacks 0H84 "homology monomorphism from a scalar-multiplication cone"]
theorem mono_homologyMap_of_cone_isGE
    {M X : DerivedCategory C} {r : R} {g : M ⟶ X}
    {δ : X ⟶ M⟦(1 : ℤ)⟧} {n i : ℤ}
    (hT : Triangle.mk (r • 𝟙 M) g δ ∈ distTriang (DerivedCategory C))
    (hX : X.IsGE (n - 1)) (hi : i < n) :
    Mono ((DerivedCategory.homologyFunctor C i).map (r • 𝟙 M)) := sorry

end SmulTriangle

end CategoryTheory.DerivedCategory
