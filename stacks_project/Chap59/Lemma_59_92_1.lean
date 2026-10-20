module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.ProperFieldExtension
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf

universe u

/- Lemma 59.92.1: if `K / k` is an extension of separably closed fields, `f : X ⟶ Spec k`
is proper, and `F` is a torsion abelian sheaf on `X` étale, then the canonical map
`etaleCohomologyRestrict (FieldExtension.toSource k K f) F q` is an isomorphism
for every `q : ℕ`. -/
@[stacks 0DDG] #check
  (AlgebraicGeometry.Scheme.Etale.etaleCohomologyRestrict_isIso_of_isProper_sepClosed :
    ∀
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [IsSepClosed k] [IsSepClosed K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    [Abelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal X.Etale]
    [(siteAbelianSectionsFunctor X.smallEtaleTopology (terminal X.Etale)).Additive]
    [Abelian (Sheaf (FieldExtension.baseChange k K f).smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions
      (Sheaf (FieldExtension.baseChange k K f).smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal (FieldExtension.baseChange k K f).Etale]
    [(siteAbelianSectionsFunctor (FieldExtension.baseChange k K f).smallEtaleTopology
      (terminal (FieldExtension.baseChange k K f).Etale)).Additive]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsLocallyTorsion F) (q : ℕ),
    IsIso (etaleCohomologyRestrict (FieldExtension.toSource k K f) F q))

end
