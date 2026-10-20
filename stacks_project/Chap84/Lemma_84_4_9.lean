module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Cohomology.ProperFieldExtension
import StacksCheckRecall

/-!
# Lemma 84.4.9

Restriction of étale cohomology of a torsion abelian sheaf on a proper algebraic
space over a separably closed field remains an isomorphism after any extension of
separably closed fields.
-/

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `etaleCohomologyRestrict`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 84.4.9: étale cohomology of a proper algebraic space with torsion
abelian coefficients is invariant under extension of separably closed fields. -/
@[stacks 0DG5] #check (AlgebraicGeometry.AlgebraicSpace.etaleCohomologyRestrict_isIso_of_proper_sepClosed :
  ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsSepClosed k] [IsSepClosed k']
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} [Proper (SchemeRealization.toBase X)]
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian
      (Sheaf (smallEtaleTopology (FieldExtension.baseChange k k' X))
        AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions
      (Sheaf (smallEtaleTopology (FieldExtension.baseChange k k' X))
        AddCommGrpCat.{u + 1})]
    [(sheafInverseImage AddCommGrpCat.{u + 1}
        (FieldExtension.baseChangeSnd k k' X)).Additive]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (hF : IsLocallyTorsion F) (q : ℕ),
    IsIso (etaleCohomologyRestrict (FieldExtension.baseChangeSnd k k' X) F q))
