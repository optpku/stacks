module

public import Mathlib.FieldTheory.IsSepClosed
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap71.Lemma_71_3_5_FieldExtension
public import stacks_project.Chap84.Lemma_84_4_9_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 84.4.9

Restriction of étale cohomology of a torsion abelian sheaf on a proper algebraic
space over a separably closed field remains an isomorphism after any extension of
separably closed fields.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `etaleCohomologyRestrict`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/-- Lemma 84.4.9: if `k'/k` is an extension of separably closed fields, `X` is a
proper algebraic space over `k`, and `F` is a torsion abelian sheaf on
`X_étale`, then the restriction map
`etaleCohomologyRestrict (FieldExtension.toSource k k' X) F q` is an isomorphism
for every `q : ℕ`. -/
@[stacks 0DG5]
theorem etaleCohomologyRestrict_isIso_of_proper_sepClosed
    (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsSepClosed k] [IsSepClosed k']
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} [Proper (toBase X)]
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian
      (Sheaf (smallEtaleTopology (FieldExtension.baseChange k k' X))
        AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions
      (Sheaf (smallEtaleTopology (FieldExtension.baseChange k k' X))
        AddCommGrpCat.{u + 1})]
    [(sheafInverseImage AddCommGrpCat.{u + 1}
        (FieldExtension.toSource k k' X)).Additive]
    [(sheafInverseImage AddCommGrpCat.{u + 1}
        (FieldExtension.toSource k k' X)).PreservesHomology]
    [(sheafInverseImage AddCommGrpCat.{u + 1}
        (FieldExtension.toSource k k' X)).PreservesInjectiveObjects]
    [(sheafInverseImage AddCommGrpCat.{u + 1} (FieldExtension.toSource k k' X) ⋙
        globalSections (FieldExtension.baseChange k k' X)).Additive]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (hF : IsLocallyTorsion F) (q : ℕ) :
    IsIso (etaleCohomologyRestrict (FieldExtension.toSource k k' X) F q) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
