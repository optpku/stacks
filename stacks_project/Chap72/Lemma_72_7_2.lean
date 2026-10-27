/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.LocallyFinite

public import Mathlib.Topology.LocallyFinite
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap72.Definition_72_4_1_Integral
public import stacks_project.Chap72.Lemma_72_7_2_Pullback
import StacksCheckRecall

/-!
# Local finiteness of prime divisors of a regular meromorphic section

On a locally Noetherian integral algebraic space, the prime divisors at which a
regular meromorphic section of an invertible module fails to lie in `L_ξ`, and
those along which its order is nonzero, form locally finite families in
`Points X`. Here `L_ξ = (Modules.pullback (fromHenselization X ξ)).obj L`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (X : AlgebraicSpace S)
variable [IsLocallyNoetherian X] [IsIntegral X]

/- Lemma 72.7.2 (1): Local finiteness of the prime divisors of a regular meromorphic section. -/
@[stacks 0EPS]
#check (AlgebraicGeometry.AlgebraicSpace.locallyFinite_primeDivisors_regularMeromorphicSection_not_regularAt :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsLocallyNoetherian X] [IsIntegral X] {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s),
    LocallyFinite fun Z : PrimeDivisor X ↦
      {x | ¬ MeromorphicSection.IsRegularAt s Z.genericPoint ∧ x ∈ Z.pointsSet})

/- Lemma 72.7.2 (2): Local finiteness of the prime divisors of a regular meromorphic section. -/
@[stacks 0EPS]
#check (AlgebraicGeometry.AlgebraicSpace.locallyFinite_regularMeromorphicSectionOrder_ne_zero :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsLocallyNoetherian X] [IsIntegral X] {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s),
    LocallyFinite fun Z : PrimeDivisor X ↦
      if MeromorphicSection.ord s hs Z = 0 then (∅ : Set (Points X)) else Z.pointsSet)

end AlgebraicGeometry.AlgebraicSpace
