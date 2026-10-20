module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidueField
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Definition 68.11.2: Let `S` be a scheme. Let `X` be a decent algebraic space over `S`.
Let `x ∈ |X|`. The residue field of `X` at `x` is the unique field `κ(x)` which comes
equipped with a monomorphism `Spec(κ(x)) ⟶ X` representing `x`. -/
@[stacks 0EMW] #check (AlgebraicGeometry.AlgebraicSpace.residueField :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S)
    [AlgebraicGeometry.AlgebraicSpace.IsDecent X]
    (x : AlgebraicGeometry.AlgebraicSpace.Points X), CommRingCat.{u})

#check (AlgebraicGeometry.AlgebraicSpace.fromSpecResidueField :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S)
    [AlgebraicGeometry.AlgebraicSpace.IsDecent X]
    (x : AlgebraicGeometry.AlgebraicSpace.Points X),
    AlgebraicGeometry.AlgebraicSpace.ofOver
      (AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint.residuePoint x).overObj ⟶ X)

#check (AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint.residuePoint_spec :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    [AlgebraicGeometry.AlgebraicSpace.IsDecent X]
    (x : AlgebraicGeometry.AlgebraicSpace.Points X),
    AlgebraicGeometry.AlgebraicSpace.QuasiCompact
        (AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint.residuePoint x).hom ∧
      Mono (AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint.residuePoint x).hom ∧
      AlgebraicGeometry.AlgebraicSpace.Points.mk
        (AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint.residuePoint x) = x)

#check (AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint.unique_iso_of_mono :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    {p q : AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint X}
    [Mono p.hom] [Mono q.hom],
    AlgebraicGeometry.AlgebraicSpace.Points.mk p =
        AlgebraicGeometry.AlgebraicSpace.Points.mk q →
      Nonempty (p ≅ q) ∧ Subsingleton (p ≅ q))
