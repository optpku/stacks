module

public import stacks_project.Chap59.Theorem_59_82_7_Gabber_Restrict
public import stacks_project.Chap59.Lemma_59_80_9_Pullback
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsSepClosed
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable [∀ Z : Scheme.{u}, Abelian (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ Z : Scheme.{u}, HasTerminal Z.Etale]
variable [∀ Z : Scheme.{u},
    (siteAbelianSectionsFunctor Z.smallEtaleTopology (terminal Z.Etale)).Additive]

/-- Lemma 59.92.1: if `K / k` is an extension of separably closed fields, `f : X ⟶ Spec k`
is proper, and `F` is a torsion abelian sheaf on `X` étale, then the canonical map
`etaleCohomologyRestrict (FieldExtension.toSource k K f) F q` is an isomorphism
for every `q : ℕ`. -/
@[stacks 0DDG]
theorem etaleCohomologyRestrict_isIso_of_isProper_sepClosed
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [IsSepClosed k] [IsSepClosed K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    [(etaleAbelianRestriction (FieldExtension.toSource k K f)).Additive]
    [(etaleAbelianRestriction (FieldExtension.toSource k K f)).PreservesHomology]
    [(etaleAbelianRestriction (FieldExtension.toSource k K f)).PreservesInjectiveObjects]
    [(etaleAbelianRestriction (FieldExtension.toSource k K f) ⋙
        siteAbelianSectionsFunctor (FieldExtension.baseChange k K f).smallEtaleTopology
          (terminal (FieldExtension.baseChange k K f).Etale)).Additive]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsLocallyTorsion F) (q : ℕ) :
    IsIso (etaleCohomologyRestrict (FieldExtension.toSource k K f) F q) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end

end
