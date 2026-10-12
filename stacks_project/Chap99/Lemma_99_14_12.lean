/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Noetherian.ULift
public import stacks_project.Chap98.Definition_98_9_4_Effective
public import stacks_project.Chap99.Lemma_99_14_8_Groupoids

/-!
# Lemma 99.14.12

The stack Polarized over `specZ` has every Artin formal object effective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- Lemma 99.14.12: the stack Polarized over the base scheme `specZ` has every
Artin formal object effective. Equivalently, every
`ξ : FormalObject toGroupoidsOverSpecZ` satisfies `FormalObject.IsEffective`. -/
@[stacks 0D4U]
instance instFormalObjectIsEffective (ξ : FormalObject toGroupoidsOverSpecZ) :
    FormalObject.IsEffective ξ :=
  sorry

/-- Every formal object of Polarized over `specZ` is isomorphic to the
approximation of some complete local object. -/
theorem exists_completeLocalObject (ξ : FormalObject toGroupoidsOverSpecZ) :
    ∃ x : CompleteLocalObject toGroupoidsOverSpecZ,
      Nonempty ((approximation toGroupoidsOverSpecZ).obj x ≅ ξ) :=
  sorry

end AlgebraicGeometry.Polarized
