/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Proper.PuncturedOpen
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 33.43.2: Let `X` be a separated, irreducible scheme of dimension `> 0` over a field
`k`. Let `x ∈ X` be a closed point. The open subscheme `X \ {x}` is not proper over `k`. -/
@[stacks 0A24] #check
  (AlgebraicGeometry.Scheme.Opens.not_isProper_comp_of_compl_closedPoint :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsSeparated f] [IrreducibleSpace X]
      (hdim : (0 : WithBot ℕ∞) < topologicalKrullDim X)
      (x : X) (hx : x ∈ closedPoints X)
      (U : X.Opens) (hU : (U : Set X) = ({x} : Set X)ᶜ),
      ¬ IsProper (U.ι ≫ f))
