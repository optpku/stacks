/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap68.Lemma_68_11_1
public import stacks_project.Chap72.Definition_72_5_2_ResidueField

/-!
# Residue fields of a good algebraic space

In Situation 82.2.1, a good algebraic space over a quasi-separated base has a
representing monomorphism from the spectrum of a field at every point, a dense
open subscheme, and residue fields agreeing along that open immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Remark 82.7.2 (1): in Situation 82.2.1, if `X / B` is good, then every point
`x` of `Points X` is represented by a monomorphism `Spec(k) ⟶ X` with `k` a
field. Uniqueness is unique factorization of monomorphic field-valued points,
by `FieldValuedPoint.iso_unique_of_mono`. Once `X` is decent, this field is
`X.residueField x` and the representing morphism is `X.fromSpecResidueField x`. -/
@[stacks 0ENW]
theorem existsMono_fieldValuedPoint_of_good {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [IsQuasiSeparated B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (x : Points X) : existsMonoFieldValuedPoint X x :=
  sorry

/-- Remark 82.7.2 (2): in Situation 82.2.1, if `X / B` is good, then `X` has a
dense open subscheme `U ⊂ X`. A canonical witness is `schematicLocus X`, by
`exists_dense_open_isScheme`. -/
@[stacks 0ENW]
theorem exists_dense_open_isScheme_of_good {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [IsQuasiSeparated B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f] :
    ∃ U : OpenSubspace X, IsScheme U.X ∧ Dense U.pointsSet :=
  sorry

/-- Remark 82.7.2 (3): in Situation 82.2.1, if `X / B` is good and `U ⊂ X` is an
open subspace which is a scheme, then for `y` in `Points U.X` the residue-field
homomorphism `Hom.residueFieldHom U.ι y` is an isomorphism. Thus
`X.residueField (Points.map U.ι y)` agrees with `U.X.residueField y`. If `U.X`
is represented by a scheme `T`, this matches the scheme residue field of the
corresponding point by `FieldValuedPoint.residuePoint_ofOver`. -/
@[stacks 0ENW]
theorem isIso_residueFieldHom_of_isScheme_openSubspace {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] [IsDecent X]
    (U : OpenSubspace X) [IsScheme U.X] [IsDecent U.X] (y : Points U.X) :
    IsIso (Hom.residueFieldHom U.ι y) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
