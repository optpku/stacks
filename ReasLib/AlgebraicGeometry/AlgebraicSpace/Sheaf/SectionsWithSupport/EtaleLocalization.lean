module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.EtaleBaseChange.Inverse
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.Composition

/-! # Étale localization of sections and cohomology with support

An étale morphism that is an isomorphism on a closed subspace preserves the higher sheaves
of sections with support and cohomology with support via the canonical restriction maps.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Adjunction

noncomputable section
universe u

-- Local instance justification (defeq pin): HasInjectiveResolutions and Functor.rightDerived require the Abelian-induced Preadditive/HasZeroMorphisms instances for definitional equality with RightDerived.postcompIso/precompIso.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace
variable {S : Scheme.{u}}

/-- An isomorphism of algebraic spaces is étale. -/
instance instEtale_inverseImageTo_of_isIso {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIso (inverseImageTo f i)] :
    Etale (inverseImageTo f i) :=
  sorry

/-- Global sections with support along a closed immersion, as the composite of the
sections-with-support functor with canonical global sections on the support. -/
abbrev gammaWithSupport {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    (sectionsWithSupport :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1}) :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  sectionsWithSupport ⋙ Sheaf.Γ (smallEtaleTopology Z) AddCommGrpCat.{u + 1}

/-- `gammaWithSupport` is sections with support followed by global sections on the support. -/
theorem gammaWithSupport_eq {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    (sectionsWithSupport :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1}) :
    gammaWithSupport i sectionsWithSupport =
      sectionsWithSupport ⋙ Sheaf.Γ (smallEtaleTopology Z) AddCommGrpCat.{u + 1} :=
  rfl

variable {X Y Z : AlgebraicSpace S} {f : X ⟶ Y} {i : Z ⟶ Y}
variable [Etale f] [IsClosedImmersion i] [IsIso (inverseImageTo f i)]

/-- The mate of the inverse étale Beck–Chevalley 2-cell of `i_*` along the support adjunctions. -/
def sectionsWithSupportEtaleBaseChangeNatTrans
    (sectionsWithSupportY :
      Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})
    (adjY : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupportY)
    (sectionsWithSupportX :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1})
    (adjX : sheafPushforward AddCommGrpCat.{u + 1} (inverseImageι f i) ⊣ sectionsWithSupportX) :
    sectionsWithSupportY ⋙
        etaleRestrictionSheaf (inverseImageTo f i) AddCommGrpCat.{u + 1} ⟶
      etaleRestrictionSheaf f AddCommGrpCat.{u + 1} ⋙ sectionsWithSupportX :=
  (mateEquiv adjY adjX
    (TwoSquare.mk _ _ _ _
      (pushforwardEtaleBaseChangeNatTransInv
        ((inverseImage_isPullback f i).flip) AddCommGrpCat.{u + 1}))).natTrans

/-- The underived comparison
`ℋ_Z(F)|_{f⁻¹(Z)} ⟶ ℋ_{f⁻¹(Z)}(F|_X)` of abelian sheaves on `f⁻¹(Z)`. -/
def sectionsWithSupportEtaleBaseChangeHom
    (sectionsWithSupportY :
      Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})
    (adjY : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupportY)
    (sectionsWithSupportX :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1})
    (adjX : sheafPushforward AddCommGrpCat.{u + 1} (inverseImageι f i) ⊣ sectionsWithSupportX)
    (F : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) :
    (etaleRestrictionSheaf (inverseImageTo f i) AddCommGrpCat.{u + 1}).obj
        (sectionsWithSupportY.obj F) ⟶
      sectionsWithSupportX.obj ((etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).obj F) :=
  (sectionsWithSupportEtaleBaseChangeNatTrans
    sectionsWithSupportY adjY sectionsWithSupportX adjX).app F

/-- The underived comparison morphism is the component of the corresponding natural
transformation. -/
theorem sectionsWithSupportEtaleBaseChangeHom_app
    (sectionsWithSupportY :
      Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})
    (adjY : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupportY)
    (sectionsWithSupportX :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1})
    (adjX : sheafPushforward AddCommGrpCat.{u + 1} (inverseImageι f i) ⊣ sectionsWithSupportX)
    (F : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) :
    sectionsWithSupportEtaleBaseChangeHom
        sectionsWithSupportY adjY sectionsWithSupportX adjX F =
      (sectionsWithSupportEtaleBaseChangeNatTrans
        sectionsWithSupportY adjY sectionsWithSupportX adjX).app F :=
  rfl

/-- The underived comparison of sections with support is an isomorphism. -/
instance isIso_sectionsWithSupportEtaleBaseChangeHom
    (sectionsWithSupportY :
      Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})
    (adjY : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupportY)
    (sectionsWithSupportX :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1})
    (adjX : sheafPushforward AddCommGrpCat.{u + 1} (inverseImageι f i) ⊣ sectionsWithSupportX)
    (F : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) :
    IsIso (sectionsWithSupportEtaleBaseChangeHom
      sectionsWithSupportY adjY sectionsWithSupportX adjX F) :=
  sorry

/-- The derived sheaf comparison
`R^q ℋ_Z(F)|_{f⁻¹(Z)} ⟶ R^q ℋ_{f⁻¹(Z)}(F|_X)` of abelian sheaves on `f⁻¹(Z)`. -/
def higherSectionsWithSupportEtaleBaseChangeHom
    (sectionsWithSupportY :
      Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})
    (adjY : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupportY)
    (sectionsWithSupportX :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1})
    (adjX : sheafPushforward AddCommGrpCat.{u + 1} (inverseImageι f i) ⊣ sectionsWithSupportX)
    [sectionsWithSupportY.Additive] [sectionsWithSupportX.Additive]
    (F : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) (q : ℕ) :
    (etaleRestrictionSheaf (inverseImageTo f i) AddCommGrpCat.{u + 1}).obj
        ((sectionsWithSupportY.rightDerived q).obj F) ⟶
      (sectionsWithSupportX.rightDerived q).obj
        ((etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).obj F) :=
  (Functor.RightDerived.postcompIso sectionsWithSupportY
        (etaleRestrictionSheaf (inverseImageTo f i) AddCommGrpCat.{u + 1}) q).inv.app F ≫
    (NatTrans.rightDerived
        (sectionsWithSupportEtaleBaseChangeNatTrans
          sectionsWithSupportY adjY sectionsWithSupportX adjX) q).app F ≫
      (Functor.RightDerived.precompIso
          (etaleRestrictionSheaf f AddCommGrpCat.{u + 1}) sectionsWithSupportX q).hom.app F

/-- The derived sheaf comparison is the `rightDerived` composite of the underived mate. -/
theorem higherSectionsWithSupportEtaleBaseChangeHom_eq
    (sectionsWithSupportY :
      Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})
    (adjY : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupportY)
    (sectionsWithSupportX :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1})
    (adjX : sheafPushforward AddCommGrpCat.{u + 1} (inverseImageι f i) ⊣ sectionsWithSupportX)
    [sectionsWithSupportY.Additive] [sectionsWithSupportX.Additive]
    (F : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) (q : ℕ) :
    higherSectionsWithSupportEtaleBaseChangeHom
        sectionsWithSupportY adjY sectionsWithSupportX adjX F q =
      (Functor.RightDerived.postcompIso sectionsWithSupportY
            (etaleRestrictionSheaf (inverseImageTo f i) AddCommGrpCat.{u + 1}) q).inv.app F ≫
        (NatTrans.rightDerived
            (sectionsWithSupportEtaleBaseChangeNatTrans
              sectionsWithSupportY adjY sectionsWithSupportX adjX) q).app F ≫
          (Functor.RightDerived.precompIso
              (etaleRestrictionSheaf f AddCommGrpCat.{u + 1})
              sectionsWithSupportX q).hom.app F :=
  rfl

/-- The canonical comparison of global sections with support, using restriction along the
isomorphism of the supports. -/
def gammaWithSupportEtaleBaseChangeNatTrans
    (sectionsWithSupportY :
      Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})
    (adjY : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupportY)
    (sectionsWithSupportX :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1})
    (adjX : sheafPushforward AddCommGrpCat.{u + 1} (inverseImageι f i) ⊣ sectionsWithSupportX) :
    gammaWithSupport i sectionsWithSupportY ⟶
      etaleRestrictionSheaf f AddCommGrpCat.{u + 1} ⋙
        gammaWithSupport (inverseImageι f i) sectionsWithSupportX :=
  whiskerLeft sectionsWithSupportY
      (etaleRestrictionSheafGlobalSectionsIso (inverseImageTo f i)).hom ≫
    whiskerRight
      (sectionsWithSupportEtaleBaseChangeNatTrans
        sectionsWithSupportY adjY sectionsWithSupportX adjX)
      (Sheaf.Γ (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1})

/-- The derived global comparison
`H^q_Z(Y, F) ⟶ H^q_{f⁻¹(Z)}(X, F|_X)` after identifying sheaves on `Z` with sheaves on
`f⁻¹(Z)` by restriction along `inverseImageTo`. -/
def cohomologyWithSupportEtaleBaseChangeHom
    (sectionsWithSupportY :
      Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})
    (adjY : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupportY)
    (sectionsWithSupportX :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1})
    (adjX : sheafPushforward AddCommGrpCat.{u + 1} (inverseImageι f i) ⊣ sectionsWithSupportX)
    [sectionsWithSupportY.Additive] [sectionsWithSupportX.Additive]
    (F : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) (q : ℕ) :
    ((gammaWithSupport i sectionsWithSupportY).rightDerived q).obj F ⟶
      ((gammaWithSupport (inverseImageι f i) sectionsWithSupportX).rightDerived q).obj
        ((etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).obj F) :=
  (NatTrans.rightDerived
        (gammaWithSupportEtaleBaseChangeNatTrans
          sectionsWithSupportY adjY sectionsWithSupportX adjX) q).app F ≫
    (Functor.RightDerived.precompIso (etaleRestrictionSheaf f AddCommGrpCat.{u + 1})
        (gammaWithSupport (inverseImageι f i) sectionsWithSupportX) q).hom.app F

/-- Étale localization preserves all higher sheaves of sections with support when the
morphism is an isomorphism on the closed support. -/
@[stacks 0A4P]
instance isIso_higherSectionsWithSupportEtaleBaseChangeHom
    (sectionsWithSupportY :
      Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})
    (adjY : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupportY)
    (sectionsWithSupportX :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1})
    (adjX : sheafPushforward AddCommGrpCat.{u + 1} (inverseImageι f i) ⊣ sectionsWithSupportX)
    [sectionsWithSupportY.Additive] [sectionsWithSupportX.Additive]
    (F : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) (q : ℕ) :
    IsIso (higherSectionsWithSupportEtaleBaseChangeHom
      sectionsWithSupportY adjY sectionsWithSupportX adjX F q) :=
  sorry

/-- Étale localization preserves cohomology with support in every degree when the
morphism is an isomorphism on the closed support. -/
@[stacks 0A4P]
instance isIso_cohomologyWithSupportEtaleBaseChangeHom
    (sectionsWithSupportY :
      Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})
    (adjY : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupportY)
    (sectionsWithSupportX :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1})
    (adjX : sheafPushforward AddCommGrpCat.{u + 1} (inverseImageι f i) ⊣ sectionsWithSupportX)
    [sectionsWithSupportY.Additive] [sectionsWithSupportX.Additive]
    (F : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) (q : ℕ) :
    IsIso (cohomologyWithSupportEtaleBaseChangeHom
      sectionsWithSupportY adjY sectionsWithSupportX adjX F q) :=
  sorry


end AlgebraicGeometry.AlgebraicSpace
