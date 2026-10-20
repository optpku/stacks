module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Definition_67_5_2_Surjective
import StacksCheckRecall

/-!
# Thickenings of algebraic spaces

Definition 76.9.1 (1), tag 05ZK, says that a thickening is a closed immersion
whose associated point spaces agree. Its canonical property and instances are
owned by `ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Definition 76.9.1 (1): A thickening is a closed immersion surjective on associated points. -/
@[stacks 05ZK] #check (AlgebraicGeometry.AlgebraicSpace.IsThickening :
  ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S}, (X ⟶ X') → Prop)

@[stacks 05ZK] #check (isThickening_iff :
  ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X'),
    IsThickening i ↔ IsClosedImmersion i ∧ Surjective i)

end AlgebraicGeometry.AlgebraicSpace
