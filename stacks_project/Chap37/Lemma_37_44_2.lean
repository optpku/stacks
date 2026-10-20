/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.FiniteNeighborhood
import StacksCheckRecall

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 37.44.2: if a proper scheme morphism has finite point-set fibre over `s`,
then it is finite after restriction to some open neighbourhood `V` of `s`; here
`f ∣_ V` denotes the restriction from the inverse-image open subscheme to `V`. -/
@[stacks 02UP] #check
  (AlgebraicGeometry.Scheme.Hom.exists_isFinite_morphismRestrict_of_finite_preimage_singleton :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.IsProper f]
      (s : S),
      Set.Finite (f ⁻¹' ({s} : Set S)) →
        ∃ V : S.Opens, s ∈ V ∧ AlgebraicGeometry.IsFinite (f ∣_ V))
