module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Injective
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap96.Lemma_96_22_1_Restriction
import StacksCheckRecall

/-!
# Lemma 96.22.1

If an algebraic stack `X` over a scheme `S` is represented by an algebraic
space `F`, restriction along `π_F = i_F⁻¹` sends injective objects of
`Ab(X_étale)` to injective objects of `Ab(F_étale)`, and sends K-injective
complexes to K-injective complexes. The analogous statements for étale
`𝒪`-modules fail.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape
open AlgebraicGeometry.GroupoidsOver
open AlgebraicGeometry.Scheme.Etale.SmallToBig.Module
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {F : AlgebraicSpace S} {X : GroupoidsOver S}
variable (e : F.toGroupoids ≌ X)

/-- Lemma 96.22.1 (1): if `I` is injective in `Ab(X_étale)`, then the
restriction `I |_{F_étale}` is injective in `Ab(F_étale)`. -/
@[stacks 075L]
theorem injective_restrictAbelian [AlgebraicStack X]
    [HasSheafify X.etaleTopology AddCommGrpCat.{u}]
    [HasSheafify (AlgebraicSpace.smallEtaleTopology F) AddCommGrpCat.{u}]
    (I : Sheaf X.etaleTopology AddCommGrpCat.{u}) [Injective I] :
    Injective ((restrictAbelian e).obj I) :=
  sorry

/-- Lemma 96.22.1 (2): if `I` is a K-injective complex in `Ab(X_étale)`, then
the restricted complex `I |_{F_étale}` is K-injective in `Ab(F_étale)`. -/
@[stacks 075L]
theorem isKInjective_restrictAbelian [AlgebraicStack X]
    [HasSheafify X.etaleTopology AddCommGrpCat.{u}]
    [HasSheafify (AlgebraicSpace.smallEtaleTopology F) AddCommGrpCat.{u}]
    (I : CochainComplex (Sheaf X.etaleTopology AddCommGrpCat.{u}) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((restrictAbelian e).mapHomologicalComplex (up ℤ)).obj I) :=
  sorry

end AlgebraicGeometry.GroupoidsOver

/- Lemma 96.22.1 (3): the corresponding statements for modules do not hold. -/
@[stacks 075L]
#check (specIntegerModulePullback_not_preservesInjective :
    ¬ specIntegerModulePullback.PreservesInjectiveObjects)
