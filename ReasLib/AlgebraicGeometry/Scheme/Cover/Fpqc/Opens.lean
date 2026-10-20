/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc

/-!
# Descent of open subsets along fpqc coverings

Compatible open subsets on the members of an fpqc covering family descend
uniquely to an open subset of the target scheme.
-/

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.FpqcCovering

/-- Pairwise-compatible open subsets on the members of an fpqc covering family
descend to a unique open subset of the target. -/
theorem existsUnique_open {T : Scheme.{u}} {ι : Type v}
    {family : ι → Over T} (hfamily : Scheme.FpqcCovering family)
    (W : (i : ι) → ((family i).left).Opens)
    (hcompat : ∀ i j : ι,
      pullback.fst (family i).hom (family j).hom ⁻¹ᵁ W i =
        pullback.snd (family i).hom (family j).hom ⁻¹ᵁ W j) :
    ∃! V : T.Opens, ∀ i : ι, W i = (family i).hom ⁻¹ᵁ V := sorry

end AlgebraicGeometry.Scheme.FpqcCovering
