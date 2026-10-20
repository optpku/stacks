module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent.Good
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.SchematicLocus.Good
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidueField.Morphism.OpenSubspace
import StacksCheckRecall

/-!
# Residue fields of a good algebraic space

In Situation 82.2.1, a good algebraic space over a quasi-separated base has a
representing monomorphism from the spectrum of a field at every point, a dense
open subscheme, and residue fields agreeing along that open immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Remark 82.7.2 (1): every point of a good algebraic space is represented by a
monomorphism from the spectrum of a field. This field is its residue field. -/
@[stacks 0ENW] #check
  (AlgebraicGeometry.AlgebraicSpace.existsMono_fieldValuedPoint_of_good :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} [IsQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f] (x : Points X),
      existsMonoFieldValuedPoint X x)

-- Monomorphic field-valued representatives of the same point are uniquely isomorphic.
#check (AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint.unique_iso_of_mono :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {p q : FieldValuedPoint X}
    [Mono p.hom] [Mono q.hom],
    Points.mk p = Points.mk q → Nonempty (p ≅ q) ∧ Subsingleton (p ≅ q))

/- Remark 82.7.2 (2): a good algebraic space contains a dense open subscheme. -/
@[stacks 0ENW] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_dense_open_isScheme_of_good :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} [IsQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f],
      ∃ U : OpenSubspace X, IsScheme U.X ∧ Dense U.pointsSet)

/- Remark 82.7.2 (3): at a point of an open scheme subspace, the residue field
agrees with that of the ambient good algebraic space. -/
@[stacks 0ENW] #check
  (AlgebraicGeometry.AlgebraicSpace.isIso_residueFieldHom_of_isScheme_openSubspace :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} [IsQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f] [IsDecent X]
      (U : OpenSubspace X) [IsScheme U.X] [IsDecent U.X] (y : Points U.X),
      IsIso (Hom.residueFieldMap U.ι y))
