/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Homotopy.Relation
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 019S

# Alternating-face complexes and simplicial homotopy

This leaf extends the zigzag simplicial-homotopy relation with its action on
alternating-face chain complexes. The direct chain homotopy for one directed
simplicial homotopy is provided by mathlib as `Homotopy.toChainHomotopy`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicTopology

universe u v

namespace CategoryTheory.SimplicialObject

variable {A : Type u} [Category.{v} A] [Preadditive A]
variable {U V : SimplicialObject A} {a b : U ⟶ V}

namespace homotopyRel.alternatingFace

/-- The alternating-face complex functor maps simplicial homotopy into chain homotopy. -/
@[stacks 019S "alternating-face functor maps homotopy relations"]
instance isMappedBy :
    HomRel.IsMappedBy (homotopyRel A) (alternatingFaceMapComplex A)
      (homotopic A (ComplexShape.down ℕ)) := sorry

end homotopyRel.alternatingFace

namespace Homotopy

namespace toChainHomotopy

/-- Equation 14.27.0.1: the degree-`n` component of the chain homotopy induced by a
simplicial homotopy is the alternating sum with the source convention `(-1) ^ (i + 1)`. -/
@[stacks 019Q "Equation 14.27.0.1"]
theorem hom_eq_alternating_sum
    (H : Homotopy a b) (n : ℕ) :
    H.toChainHomotopy.hom n (n + 1) =
      ∑ i : Fin (n + 1), ((-1 : ℤ) ^ ((i : ℕ) + 1)) • H.h i := sorry

end toChainHomotopy

end Homotopy

namespace Homotopic

/-- Zigzag-homotopic simplicial morphisms induce the canonical chain-homotopy relation on
alternating-face complexes. -/
@[stacks 019S "homotopy invariance of alternating-face complexes"]
theorem alternatingFace (hab : Homotopic a b) :
    homotopic A (ComplexShape.down ℕ)
      ((alternatingFaceMapComplex A).map a)
      ((alternatingFaceMapComplex A).map b) := sorry

end Homotopic

end CategoryTheory.SimplicialObject
