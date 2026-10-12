/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Flasque presheaves

The Mathlib owner `TopCat.Presheaf.IsFlasque` is categorical: every restriction morphism is an
epimorphism.  This leaf records the elementwise surjectivity bridge for set-valued presheaves.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace TopCat

universe u v

namespace TopCat.Presheaf

variable {X : TopCat.{u}}

/-- A flasque set-valued presheaf has surjective restriction maps on all inclusions of opens. -/
@[stacks 09SW "surjective restriction maps"]
theorem IsFlasque.restriction_surjective
    {F : X.Presheaf (Type v)} (hF : IsFlasque F)
    {U V : Opens X} (hUV : U ≤ V) :
    Function.Surjective (F.map (homOfLE hUV).op) := sorry

/-- A set-valued presheaf is flasque exactly when all its restriction maps are surjective. -/
@[stacks 09SW "surjective restriction characterization"]
theorem isFlasque_iff_restriction_surjective
    (F : X.Presheaf (Type v)) :
    IsFlasque F ↔
      ∀ ⦃U V : Opens X⦄ (hUV : U ≤ V), Function.Surjective (F.map (homOfLE hUV).op) := sorry

end TopCat.Presheaf
