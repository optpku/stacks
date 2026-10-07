module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Modification
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap68.Definition_68_22_1_Birational
public import stacks_project.Chap72.Definition_72_8_1_Integral

/-!
# Modifications of integral algebraic spaces

A modification is a birational proper morphism of integral algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A modification is a birational proper morphism between integral algebraic
spaces. -/
class IsModification {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    [IsIntegral X'] [IsIntegral X] (f : X' ⟶ X) : Prop
    extends Proper f, IsBirational f

/-- Over integral source and target algebraic spaces, a morphism is a
modification if and only if it is birational and proper. -/
theorem isModification_iff {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    [IsIntegral X'] [IsIntegral X] (f : X' ⟶ X) :
    IsModification f ↔ IsBirational f ∧ Proper f :=
  sorry

/-- The identity morphism of an integral algebraic space is a modification. -/
instance instIsModification_id {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsIntegral X] : IsModification (𝟙 X) :=
  sorry

/-- A modification of schemes over `S` induces a modification of the associated
algebraic spaces. -/
instance instIsModification_ofOverMap {S : Scheme.{u}} {U V : Over S}
    (f : U ⟶ V) [AlgebraicGeometry.IsModification f.left] :
    IsModification (ofOverMap f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
