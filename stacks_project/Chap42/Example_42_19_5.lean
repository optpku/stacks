module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveLineChain

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveLineChain

variable (k : Type u) [Field k] {X : Scheme.{u}}
variable (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
variable (components : ℕ → (ProjectiveLine.scheme k ⟶ X))
variable [∀ j, IsClosedImmersion (components j)]

/- Example 42.19.5 (1): for a locally finite covering chain of projective lines whose infinity
point on each component is identified with the zero point on the next, the origin cycle on the
first component is rationally equivalent to zero. -/
@[stacks 02RY] #check
  (AlgebraicGeometry.ProjectiveLineChain.origin_rationallyEquivalent_zero k p components :
    (h_over : ∀ j, components j ≫ p = ProjectiveLine.toSpec k) →
    (h_local : LocallyFinite fun j ↦ Set.range (components j).base) →
    (h_node : ∀ j, (components j).base (ProjectiveLine.infinityPoint k) =
      (components (j + 1)).base (ProjectiveLine.zeroPoint k)) →
    (h_cover : ∀ x : X, ∃ j y, (components j).base y = x) →
    @RationalEquivalence.RationallyEquivalent X
      (LocallyOfFiniteType.isLocallyNoetherian p)
      (p.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ (0 : ℤ))) inferInstance 0
      (originCycle k p components h_over) 0)

/- Example 42.19.5 (2): for the same chain, every degree-zero Chow class is zero. -/
@[stacks 02RY] #check
  (AlgebraicGeometry.ProjectiveLineChain.chowGroup_eq_zero k p components :
    (h_over : ∀ j, components j ≫ p = ProjectiveLine.toSpec k) →
    (h_local : LocallyFinite fun j ↦ Set.range (components j).base) →
    (h_node : ∀ j, (components j).base (ProjectiveLine.infinityPoint k) =
      (components (j + 1)).base (ProjectiveLine.zeroPoint k)) →
    (h_cover : ∀ x : X, ∃ j y, (components j).base y = x) →
    ∀ a : @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
      (p.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ (0 : ℤ))) inferInstance 0,
      a = 0)

end AlgebraicGeometry.ProjectiveLineChain
