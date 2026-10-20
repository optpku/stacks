module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.SeparablyClosedFieldExtension
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf

noncomputable section

universe w u

namespace AlgebraicGeometry.Scheme.Etale

variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B),
    ((smallEtalePullback h).sheafPushforwardContinuous AddCommGrpCat.{u}
      B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]
variable [∀ Z : Scheme.{u},
    HasDerivedCategory.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ Z : Scheme.{u},
    ((siteAbelianSectionsFunctor Z.smallEtaleTopology (globalEtale Z)).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}))]

/- Lemma 59.90.2 (1): if `K / k` is an extension of separably closed fields, `f : X ⟶ Spec k`
is quasi-compact and quasi-separated, and `E ∈ D⁺(X_étale)` has cohomology sheaves whose
geometric stalks are torsion of orders invertible in `k`, then the canonical restriction
`H^q_étale(X, E) ⟶ H^q_étale(X_K, E|_{X_K})` is an isomorphism for every `q : ℤ`. Here
`X_K = FieldExtension.baseChange k K f`, the comparison morphism is
`FieldExtension.toSource k K f`, the restriction `E|_{X_K}` is
`(etaleDerivedInverseImage (FieldExtension.toSource k K f)).obj E`, and the map is
`derivedEtaleCohomologyRestrict`. -/
@[stacks 0F0B] #check (AlgebraicGeometry.Scheme.Etale.derivedEtaleCohomologyRestrict_isIso_of_sepClosedFieldExtension :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    [IsSepClosed k] [IsSepClosed K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [QuasiCompact f] [QuasiSeparated f]
    [(etaleAbelianSheafPullback (FieldExtension.toSource k K f)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [(etaleAbelianSheafPullback (FieldExtension.toSource k K f) ⋙
        siteAbelianSectionsFunctor
          (FieldExtension.baseChange k K f).smallEtaleTopology
          (globalEtale (FieldExtension.baseChange k K f))).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (hE : DerivedCategory.Plus.cohomologyIn
      (IsTorsionWithOrdersInvertibleOn (Spec (CommRingCat.of k)) :
        ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) E)
    (q : ℤ),
    IsIso (derivedEtaleCohomologyRestrict (FieldExtension.toSource k K f) E q))

/- Lemma 59.90.2 (2): in the same situation, the derived adjunction unit
`E ⟶ R(X_K → X)_* (E|_{X_K})` is an isomorphism, where
`R(X_K → X)_* = etaleDerivedPushforward (FieldExtension.toSource k K f)` and
`E|_{X_K} = (etaleDerivedInverseImage (FieldExtension.toSource k K f)).obj E`. -/
@[stacks 0F0B] #check (AlgebraicGeometry.Scheme.Etale.etaleDerivedAdjunctionUnit_isIso_of_sepClosedFieldExtension :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    [IsSepClosed k] [IsSepClosed K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [QuasiCompact f] [QuasiSeparated f]
    [(abelianPushforwardAlong (FieldExtension.toSource k K f)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (FieldExtension.baseChange k K f).smallEtaleTopology AddCommGrpCat.{u}))]
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (hE : DerivedCategory.Plus.cohomologyIn
      (IsTorsionWithOrdersInvertibleOn (Spec (CommRingCat.of k)) :
        ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) E),
    IsIso (etaleDerivedAdjunctionUnit (FieldExtension.toSource k K f) E))

end AlgebraicGeometry.Scheme.Etale

end

end
