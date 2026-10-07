module

public import stacks_project.Chap69.Lemma_69_9_3_Comparison

/-!
# Lemma 69.9.3

Étale localization of cohomology with support in a closed subspace of an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits CategoryTheory.Functor

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived`
-- pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of
-- `higherSectionsWithSupportEtaleBaseChangeHom` and
-- `cohomologyWithSupportEtaleBaseChangeHom`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
variable {f : X ⟶ Y} {i : Z ⟶ Y}
variable [Etale f] [IsClosedImmersion i] [IsIso (inverseImageTo f i)]

/-- Lemma 69.9.3 (1): if `f : X ⟶ Y` is étale over a scheme `S` and `i : Z ⟶ Y` is a closed
immersion with `f⁻¹(Z) ⟶ Z` an isomorphism, then for an abelian sheaf `F` on `Y_étale` one has
`ℋ^q_Z(F) ≅ ℋ^q_{f⁻¹(Z)}(F|_X)` as sheaves on `Z` and `f⁻¹(Z)`, identified by restriction along
`inverseImageTo`. -/
@[stacks 0A4P]
theorem isIso_higherSectionsWithSupportEtaleBaseChangeHom
    (sectionsWithSupportY :
      Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})
    (adjY : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupportY)
    (sectionsWithSupportX :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1})
    (adjX : sheafPushforward AddCommGrpCat.{u + 1} (inverseImageι f i) ⊣ sectionsWithSupportX)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology Z) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1}]
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [sectionsWithSupportY.Additive] [sectionsWithSupportX.Additive]
    [(etaleRestrictionSheaf (inverseImageTo f i) AddCommGrpCat.{u + 1}).Additive]
    [(etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).Additive]
    [(etaleRestrictionSheaf (inverseImageTo f i) AddCommGrpCat.{u + 1}).PreservesHomology]
    [(etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).PreservesHomology]
    [(etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).PreservesInjectiveObjects]
    (F : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) (q : ℕ) :
    IsIso (higherSectionsWithSupportEtaleBaseChangeHom
      sectionsWithSupportY adjY sectionsWithSupportX adjX F q) :=
  sorry

/-- Lemma 69.9.3 (2): in the situation of (1), the derived global groups with support are
isomorphic: `H^q_Z(Y, F) ≅ H^q_{f⁻¹(Z)}(X, F|_X)`, after identifying sheaves on `Z` with sheaves
on `f⁻¹(Z)` by restriction along `inverseImageTo`. -/
@[stacks 0A4P]
theorem isIso_cohomologyWithSupportEtaleBaseChangeHom
    (sectionsWithSupportY :
      Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})
    (adjY : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupportY)
    (sectionsWithSupportX :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1})
    (adjX : sheafPushforward AddCommGrpCat.{u + 1} (inverseImageι f i) ⊣ sectionsWithSupportX)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology Z) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [sectionsWithSupportY.Additive] [sectionsWithSupportX.Additive]
    [(etaleRestrictionSheaf (inverseImageTo f i) AddCommGrpCat.{u + 1}).Additive]
    [(etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).Additive]
    [(etaleRestrictionSheaf (inverseImageTo f i) AddCommGrpCat.{u + 1}).PreservesHomology]
    [(etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).PreservesHomology]
    [(etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).PreservesInjectiveObjects]
    [(Sheaf.functorH (smallEtaleTopology (inverseImage f i)) 0).Additive]
    [(gammaWithSupport (inverseImageι f i) sectionsWithSupportX).Additive]
    (F : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) (q : ℕ) :
    IsIso (cohomologyWithSupportEtaleBaseChangeHom
      sectionsWithSupportY adjY sectionsWithSupportX adjX F q) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
