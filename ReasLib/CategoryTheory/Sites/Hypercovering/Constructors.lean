/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.FixedTarget

/-!
# Constructors for hypercoverings

This leaf provides the direct constructor and projection API for hypercoverings from an
underlying simplicial fixed-target formal coproduct family.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory

open Opposite
open Limits
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {J : GrothendieckTopology C}

namespace Hypercovering

variable {X : C}

/-- Definition 25.3.3: build a hypercovering from a simplicial fixed-target family, its
degree-zero covering condition, and its covering matching maps. -/
def ofSimplicial (K : SimplicialObject (SemiRepresentableFamily.OverFamily.{v, u, w} X))
    (zero_isCovering : (K.obj (op <| SimplexCategory.mk 0)).toSieve ∈ J X)
    (succ_isCovering : ∀ n : ℕ,
      SemiRepresentableFamily.OverFamily.covering J
        (SimplicialObject.matchingMap K n)) :
    Hypercovering.{w} J X where
  toSimplicialObject := K
  zero_isCovering := zero_isCovering
  succ_isCovering := succ_isCovering

/-- The constructor retains its supplied underlying simplicial object. -/
@[simp] theorem ofSimplicial_toSimplicialObject
    (K : SimplicialObject (SemiRepresentableFamily.OverFamily.{v, u, w} X))
    (zero_isCovering : (K.obj (op <| SimplexCategory.mk 0)).toSieve ∈ J X)
    (succ_isCovering : ∀ n : ℕ,
      SemiRepresentableFamily.OverFamily.covering J
        (SimplicialObject.matchingMap K n)) :
    (ofSimplicial K zero_isCovering succ_isCovering).toSimplicialObject = K := sorry

/-- The constructor retains its supplied degree-zero covering condition. -/
@[simp] theorem ofSimplicial_zero_isCovering
    (K : SimplicialObject (SemiRepresentableFamily.OverFamily.{v, u, w} X))
    (zero_isCovering : (K.obj (op <| SimplexCategory.mk 0)).toSieve ∈ J X)
    (succ_isCovering : ∀ n : ℕ,
      SemiRepresentableFamily.OverFamily.covering J
        (SimplicialObject.matchingMap K n)) :
    (ofSimplicial K zero_isCovering succ_isCovering).zero_isCovering = zero_isCovering := sorry

/-- The constructor retains each supplied higher matching-map covering condition. -/
@[simp] theorem ofSimplicial_succ_isCovering
    (K : SimplicialObject (SemiRepresentableFamily.OverFamily.{v, u, w} X))
    (zero_isCovering : (K.obj (op <| SimplexCategory.mk 0)).toSieve ∈ J X)
    (succ_isCovering : ∀ n : ℕ,
      SemiRepresentableFamily.OverFamily.covering J
        (SimplicialObject.matchingMap K n))
    (n : ℕ) :
    (ofSimplicial K zero_isCovering succ_isCovering).succ_isCovering n =
      succ_isCovering n := sorry

end Hypercovering

end CategoryTheory
