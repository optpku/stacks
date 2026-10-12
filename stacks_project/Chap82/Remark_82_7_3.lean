/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap66.Lemma_66_12_3
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap72.Definition_72_4_1_Integral
public import stacks_project.Chap72.Definition_72_5_2_ResidueField
public import stacks_project.Chap72.Lemma_72_4_2_Comparison
import StacksCheckRecall

/-!
# Function fields of good integral algebraic spaces

In Situation 82.2.1, if `X / B` is good and `X` is integral, the function field
`R(X)` is the residue field at the generic point of `X`. For any point `x`,
`κ(x)` is the function field of the unique integral closed subspace through `x`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Remark 82.7.3 (1): in Situation 82.2.1, if `X / B` is good and `X` is
integral, the function field `R(X)` is defined as `RationalFunction X` with
`Field` instance `instField_rationalFunctionRing`, and equals the residue field
of `X` at a generic point via `rationalFunctionRingEquivResidueField`, i.e.
`RationalFunction X ≃+* ULift (X.residueField η)` for `η ∈ genericPoints X`.
See Spaces over Fields, Definition 72.4.3. -/
@[stacks 0ENX] #check instField_rationalFunctionRing
@[stacks 0ENX] #check rationalFunctionRingEquivResidueField

/-- Remark 82.7.3 (2): in Situation 82.2.1, if `X / B` is good and `X` is
integral, then for any `x` in `Points X` the residue field `X.residueField x`
is the function field of the unique integral closed subspace `Z ⊂ X` whose
generic point is `x`. Uniqueness of `Z` is `existsUnique_integralClosedSubspace`.
If `IsGenericPoint x Z.pointsSet` and `Points.map Z.ι η = x`, then
`Hom.residueFieldHom Z.ι η` is an isomorphism, so `X.residueField x` agrees
with `Z.X.residueField η`. Combined with `rationalFunctionRingEquivResidueField`
on `Z.X`, this identifies `X.residueField x` with `RationalFunction Z.X`. -/
@[stacks 0ENX]
theorem isIso_residueFieldHom_of_integralClosedSubspace {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] [IsIntegral X] (x : Points X)
    (Z : ClosedSubspace X) [IsIntegral Z.X] (hZ : IsGenericPoint x Z.pointsSet)
    {η : Points Z.X} (hmap : Points.map Z.ι η = x) :
    IsIso (Hom.residueFieldHom Z.ι η) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
