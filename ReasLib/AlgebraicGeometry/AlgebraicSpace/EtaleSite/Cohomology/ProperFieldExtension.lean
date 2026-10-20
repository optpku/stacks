/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Cohomology.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldExtension.Galois
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import Mathlib.FieldTheory.IsSepClosed

/-!
# Proper algebraic spaces over separably closed fields

Restriction along an extension of separably closed fields preserves étale
cohomology of a proper algebraic space with locally torsion abelian coefficients.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `etaleCohomologyRestrict`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/-- For a proper algebraic space over a separably closed field, restriction
along an extension to a separably closed field is an isomorphism on étale
cohomology with locally torsion abelian coefficients in every nonnegative degree. -/
theorem etaleCohomologyRestrict_isIso_of_proper_sepClosed
    (k k' : Type u) [Field k] [Field k'] [Algebra k k']
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
    (hF : IsLocallyTorsion F) (q : ℕ) :
    IsIso (etaleCohomologyRestrict (FieldExtension.baseChangeSnd k k' X) F q) :=
  sorry

/-- Local torsion supplied as a fact makes cohomology restriction along an
extension of separably closed fields an isomorphism for a proper algebraic space. -/
instance etaleCohomologyRestrict_isIso_of_proper_sepClosed_of_fact
    (k k' : Type u) [Field k] [Field k'] [Algebra k k']
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
    [Fact (IsLocallyTorsion F)] (q : ℕ) :
    IsIso (etaleCohomologyRestrict (FieldExtension.baseChangeSnd k k' X) F q) :=
  etaleCohomologyRestrict_isIso_of_proper_sepClosed k k' F Fact.out q

end AlgebraicGeometry.AlgebraicSpace
