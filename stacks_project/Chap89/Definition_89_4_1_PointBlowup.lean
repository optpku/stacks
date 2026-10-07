module

public import stacks_project.Chap68.Lemma_68_14_6
public import stacks_project.Chap71.Definition_71_17_1_Blowup

/-!
# Blowing up a decent algebraic space at a closed point

A closed point of a decent algebraic space is represented by the residue-field
closed immersion `fromSpecResidueField`. The blowup at that point is the blowup
along the corresponding closed subspace.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ClosedSubspace

/-- The closed subspace of a decent algebraic space cut out by the residue-field
closed immersion representing a closed point. -/
noncomputable def ofClosedPoint {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (x : Points X) (hx : x ∈ closedPoints (Points X)) : ClosedSubspace X :=
  { X := ofOver (FieldValuedPoint.residuePoint x).overObj
    ι := X.fromSpecResidueField x
    isClosedImmersion := isClosedImmersion_fromSpecResidueField hx }

/-- The inclusion of the residue-field closed subspace is the residue-field
morphism `fromSpecResidueField`. -/
theorem ofClosedPoint_ι {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (x : Points X) (hx : x ∈ closedPoints (Points X)) :
    (ofClosedPoint x hx).ι = X.fromSpecResidueField x :=
  sorry

/-- The residue-field closed subspace is the closed immersion representing the
given closed point. -/
theorem ofClosedPoint_spec {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (x : Points X) (hx : x ∈ closedPoints (Points X)) :
    IsClosedImmersion (ofClosedPoint x hx).ι ∧
      (ofClosedPoint x hx).ι = X.fromSpecResidueField x ∧
      Points.mk (FieldValuedPoint.residuePoint x) = x :=
  sorry

end ClosedSubspace

namespace Blowup

/-- The blowing up of a decent algebraic space at a closed point is the blowing
up along the residue-field closed subspace representing that point. -/
abbrev atPoint {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (x : Points X) (hx : x ∈ closedPoints (Points X)) :=
  Blowup.along (ClosedSubspace.ofClosedPoint x hx)

/-- Blowing up at a closed point is blowing up along the residue-field closed
subspace of that point. -/
theorem atPoint_eq {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (x : Points X) (hx : x ∈ closedPoints (Points X)) :
    atPoint x hx = Blowup.along (ClosedSubspace.ofClosedPoint x hx) :=
  sorry

end Blowup

end AlgebraicGeometry.AlgebraicSpace
