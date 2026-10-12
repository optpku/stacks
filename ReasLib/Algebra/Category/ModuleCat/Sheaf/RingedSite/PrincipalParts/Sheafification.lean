/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SheafificationAdjunction
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.PrincipalParts.BaseChange
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialOperator.Sheafification
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.Construction

/-!
# Principal parts and sheafification

This file compares the two canonical ways to pass sectionwise principal parts to sheaves:
sheafifying the principal-parts presheaf of the original data, and first sheafifying the rings
and module and then taking their principal-parts sheaf.

Both comparison directions are explicit.  The reverse map classifies the universal differential
obtained by sheafifying the sectionwise universal differential, so downstream users can work
with the map and its universal-property API without extracting data from an `IsIso` proof.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.PrincipalParts.Sheafification

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{max u v}}

/-- The morphism of commutative-ring sheaves induced by a morphism of commutative-ring
presheaves. -/
abbrev sheafifiedRingMap (phi : O₁ ⟶ O₂) :
    PresheafOfModules.commRingSheafification J O₁ ⟶
      PresheafOfModules.commRingSheafification J O₂ :=
  PresheafOfModules.commRingSheafificationMap J phi

/-- The module sheaf obtained by sheafifying a module presheaf over a commutative-ring
presheaf. -/
abbrev sheafifiedModule (F : PresheafOfModules (ringPresheaf O₂)) :
    ringedSiteModuleCategory J (PresheafOfModules.commRingSheafification J O₂) :=
  (PresheafOfModules.moduleSheafification J O₂).obj F

/-- The sheafification of the objectwise principal-parts presheaf of the original data. -/
abbrev ofPresheaf (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    ringedSiteModuleCategory J (PresheafOfModules.commRingSheafification J O₂) :=
  (PresheafOfModules.moduleSheafification J O₂).obj
    (PresheafOfModules.PrincipalParts.presheaf phi F k)

/-- The principal-parts presheaf formed after sheafifying the rings and the module. -/
abbrev presheafAfterSheafification (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    PresheafOfModules
      (ringSheaf J (PresheafOfModules.commRingSheafification J O₂)).obj :=
  presheaf (sheafifiedRingMap J phi) (sheafifiedModule J F) k

/-- The canonical principal-parts sheaf formed after sheafifying the rings and the module. -/
abbrev afterSheafification (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    ringedSiteModuleCategory J (PresheafOfModules.commRingSheafification J O₂) :=
  sheaf (sheafifiedRingMap J phi) (sheafifiedModule J F) k

/-- The natural base-change morphism from the original principal-parts presheaf to the
restriction of the principal-parts presheaf of the sheafified data. -/
noncomputable def unitBaseChange (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    PresheafOfModules.PrincipalParts.presheaf phi F k ⟶
      (PresheafOfModules.restrictScalars
        (PresheafOfModules.sheafificationRingMap J O₂)).obj
        (presheafAfterSheafification J phi F k) :=
  PresheafOfModules.PrincipalParts.BaseChange.map
    (PresheafOfModules.commRingSheafificationSquare J phi)
    ((PresheafOfModules.moduleSheafificationUnit J O₂).app F) k

/-- The adjunction-side morphism defining the comparison of the two principal-parts
sheafifications. -/
noncomputable def comparisonUnit (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    PresheafOfModules.PrincipalParts.presheaf phi F k ⟶
      (PresheafOfModules.restrictScalars
        (PresheafOfModules.sheafificationRingMap J O₂)).obj
        (afterSheafification J phi F k).val :=
  unitBaseChange J phi F k ≫
    (PresheafOfModules.restrictScalars
      (PresheafOfModules.sheafificationRingMap J O₂)).map
      (moduleSheafificationUnitToVal
        (PresheafOfModules.commRingSheafification J O₂)
        (presheafAfterSheafification J phi F k))

/-- The canonical comparison from sheafified objectwise principal parts to principal parts of
the sheafified rings and module. -/
@[stacks 09CV "comparison morphism", stacks 0G3U "comparison morphism"]
noncomputable def comparison (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    ofPresheaf J phi F k ⟶ afterSheafification J phi F k :=
  (PresheafOfModules.sheafificationHomEquiv
    (PresheafOfModules.sheafificationRingMap J O₂)).symm
      (comparisonUnit J phi F k)

/-- Under the module-sheafification adjunction, the canonical comparison is exactly the
sectionwise base-change map followed by the post-sheafification presentation unit. -/
@[simp, stacks 09CV "adjunction characterization", stacks 0G3U "adjunction characterization"]
theorem comparison_adj (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    PresheafOfModules.sheafificationHomEquiv
        (PresheafOfModules.sheafificationRingMap J O₂)
        (comparison J phi F k) =
      comparisonUnit J phi F k := sorry

/-- The source-side universal differential obtained by sheafifying the sectionwise universal
differential after restriction of scalars. -/
@[stacks 09CV "source universal differential", stacks 0G3U "source universal differential"]
noncomputable def sourceOperatorHom (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    (restrictionAlong (sheafifiedRingMap J phi)).obj (sheafifiedModule J F) ⟶
      (restrictionAlong (sheafifiedRingMap J phi)).obj (ofPresheaf J phi F k) :=
  PresheafOfModules.ModuleSheafification.mapAfterRestriction J phi
    (PresheafOfModules.PrincipalParts.universalDifferential phi F k)

/-- Sheafification preserves the order bound on the source-side universal differential. -/
@[stacks 09CV "source universal differential order",
  stacks 0G3U "source universal differential order"]
theorem sourceOperatorHom_isOrderLE (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    IsDifferentialOperatorOfOrder (sheafifiedRingMap J phi)
      (sourceOperatorHom J phi F k) k := sorry

/-- The bounded differential operator represented by the sheafification of sectionwise
principal parts. -/
@[stacks 09CV "source bounded differential operator",
  stacks 0G3U "source bounded differential operator"]
noncomputable def sourceOperator (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    DifferentialOperators.ofOrder (sheafifiedRingMap J phi)
      (sheafifiedModule J F) k (ofPresheaf J phi F k) :=
  DifferentialOperators.ofHom (sourceOperatorHom J phi F k)
    (sourceOperatorHom_isOrderLE J phi F k)

/-- The morphism underlying `sourceOperator` is the sheafified sectionwise universal
differential. -/
@[simp]
theorem sourceOperator_toHom (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    DifferentialOperators.toHom (sourceOperator J phi F k) =
      sourceOperatorHom J phi F k := sorry

/-- The explicit inverse comparison, obtained by universal descent from principal parts after
sheafification to the sheafification of sectionwise principal parts. -/
@[stacks 09CV "inverse comparison morphism", stacks 0G3U "inverse comparison morphism"]
noncomputable def comparisonInv (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    afterSheafification J phi F k ⟶ ofPresheaf J phi F k :=
  desc
    (corepresentation (sheafifiedRingMap J phi) (sheafifiedModule J F) k)
    (sourceOperatorHom J phi F k) (sourceOperatorHom_isOrderLE J phi F k)

/-- The inverse comparison is exactly the universal descent classified by the source-side
bounded differential operator. -/
@[stacks 09CV "inverse comparison by universal descent",
  stacks 0G3U "inverse comparison by universal descent"]
theorem comparisonInv_desc (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    comparisonInv J phi F k =
      desc (corepresentation (sheafifiedRingMap J phi) (sheafifiedModule J F) k)
        (sourceOperatorHom J phi F k) (sourceOperatorHom_isOrderLE J phi F k) := sorry

/-- Postcomposing the source-side universal differential with the forward comparison gives the
canonical universal operator after sheafification. -/
@[stacks 09CV "forward comparison on universal operators",
  stacks 0G3U "forward comparison on universal operators"]
theorem sourceOperatorHom_comparison (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    sourceOperatorHom J phi F k ≫
        (restrictionAlong (sheafifiedRingMap J phi)).map (comparison J phi F k) =
      universalOperator
        (corepresentation (sheafifiedRingMap J phi) (sheafifiedModule J F) k) := sorry

/-- The universal operator after sheafification factors through the explicit inverse
comparison as the source-side universal differential. -/
@[stacks 09CV "inverse comparison on universal operators",
  stacks 0G3U "inverse comparison on universal operators"]
theorem universalOperator_comparisonInv (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    universalOperator
          (corepresentation (sheafifiedRingMap J phi) (sheafifiedModule J F) k) ≫
        (restrictionAlong (sheafifiedRingMap J phi)).map (comparisonInv J phi F k) =
      sourceOperatorHom J phi F k := sorry

/-- The forward comparison followed by the explicit reverse comparison is the identity. -/
@[simp, stacks 09CV "forward-inverse comparison law",
  stacks 0G3U "forward-inverse comparison law"]
theorem comparison_comp_comparisonInv (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    comparison J phi F k ≫ comparisonInv J phi F k =
      𝟙 (ofPresheaf J phi F k) := sorry

/-- The explicit reverse comparison followed by the forward comparison is the identity. -/
@[simp, stacks 09CV "inverse-forward comparison law",
  stacks 0G3U "inverse-forward comparison law"]
theorem comparisonInv_comp_comparison (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    comparisonInv J phi F k ≫ comparison J phi F k =
      𝟙 (afterSheafification J phi F k) := sorry

/-- Lemma 18.34.5 (09CV), Lemma 17.29.5 (0G3U): the canonical comparison from the
sheafification of sectionwise principal parts to principal parts after sheafification is an
isomorphism, witnessed by `comparisonInv`. -/
@[stacks 09CV "comparison is an isomorphism", stacks 0G3U "comparison is an isomorphism"]
instance comparison_isIso (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    IsIso (comparison J phi F k) :=
  IsIso.mk ⟨comparisonInv J phi F k, comparison_comp_comparisonInv J phi F k,
    comparisonInv_comp_comparison J phi F k⟩

/-- Lemma 18.34.5 (09CV), Lemma 17.29.5 (0G3U): the canonical isomorphism from sheafified
sectionwise principal parts to principal parts formed after sheafification. -/
@[stacks 09CV, stacks 0G3U]
noncomputable def comparisonIso (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    ofPresheaf J phi F k ≅ afterSheafification J phi F k :=
  { hom := comparison J phi F k
    inv := comparisonInv J phi F k
    hom_inv_id := comparison_comp_comparisonInv J phi F k
    inv_hom_id := comparisonInv_comp_comparison J phi F k }

/-- The forward map of the principal-parts sheafification isomorphism is the canonical
comparison. -/
@[simp]
theorem comparisonIso_hom (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    (comparisonIso J phi F k).hom = comparison J phi F k := sorry

/-- The inverse map of the principal-parts sheafification isomorphism is the explicit universal
descent comparison. -/
@[stacks 09CV "inverse comparison morphism", stacks 0G3U "inverse comparison morphism", simp]
theorem comparisonIso_inv (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    (comparisonIso J phi F k).inv = comparisonInv J phi F k := sorry

/-- The inverse extracted from the `IsIso` instance agrees with the explicit universal descent
comparison. -/
@[simp]
theorem inv_comparison (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    inv (comparison J phi F k) = comparisonInv J phi F k := sorry

/-- Under the sheafification adjunction, the forward map of `comparisonIso` is the sectionwise
base-change map followed by the post-sheafification presentation unit. -/
theorem comparisonIso_hom_adj (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    PresheafOfModules.sheafificationHomEquiv
        (PresheafOfModules.sheafificationRingMap J O₂)
        (comparisonIso J phi F k).hom =
      comparisonUnit J phi F k := sorry

/-- The functor that takes sectionwise principal parts and then sheafifies. -/
@[stacks 09CV "sheafified sectionwise principal-parts functor",
  stacks 0G3U "sheafified sectionwise principal-parts functor"]
noncomputable def sourceFunctor (phi : O₁ ⟶ O₂) (k : ℕ) :
    PresheafOfModules (ringPresheaf O₂) ⥤
      ringedSiteModuleCategory J (PresheafOfModules.commRingSheafification J O₂) :=
  PresheafOfModules.PrincipalParts.functor phi k ⋙
    PresheafOfModules.moduleSheafification J O₂

/-- The functor that first sheafifies a module presheaf and then takes principal parts. -/
@[stacks 09CV "principal parts after sheafification functor",
  stacks 0G3U "principal parts after sheafification functor"]
noncomputable def targetFunctor (phi : O₁ ⟶ O₂) (k : ℕ) :
    PresheafOfModules (ringPresheaf O₂) ⥤
      ringedSiteModuleCategory J (PresheafOfModules.commRingSheafification J O₂) :=
  PresheafOfModules.moduleSheafification J O₂ ⋙
    SheafOfModules.RingedSite.PrincipalParts.functor (sheafifiedRingMap J phi) k

/-- The object of `sourceFunctor` is the sheafification of sectionwise principal parts. -/
theorem sourceFunctor_obj (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    (sourceFunctor J phi k).obj F = ofPresheaf J phi F k := sorry

/-- The object of `targetFunctor` is principal parts formed after sheafification. -/
theorem targetFunctor_obj (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    (targetFunctor J phi k).obj F = afterSheafification J phi F k := sorry

/-- The objectwise principal-parts comparisons are natural in the module presheaf. -/
@[stacks 09CV "comparison naturality", stacks 0G3U "comparison naturality"]
theorem comparison_naturality (phi : O₁ ⟶ O₂) (k : ℕ)
    {F G : PresheafOfModules (ringPresheaf O₂)} (f : F ⟶ G) :
    (sourceFunctor J phi k).map f ≫ comparison J phi G k =
      comparison J phi F k ≫ (targetFunctor J phi k).map f := sorry

/-- The explicit inverse comparisons are natural in the module presheaf. -/
@[stacks 09CV "inverse comparison naturality", stacks 0G3U "inverse comparison naturality"]
theorem comparisonInv_naturality (phi : O₁ ⟶ O₂) (k : ℕ)
    {F G : PresheafOfModules (ringPresheaf O₂)} (f : F ⟶ G) :
    (targetFunctor J phi k).map f ≫ comparisonInv J phi G k =
      comparisonInv J phi F k ≫ (sourceFunctor J phi k).map f := sorry

/-- The natural comparison from sheafified sectionwise principal parts to principal parts after
sheafification. -/
@[stacks 09CV "natural comparison", stacks 0G3U "natural comparison"]
noncomputable def comparisonNatTrans (phi : O₁ ⟶ O₂) (k : ℕ) :
    sourceFunctor J phi k ⟶ targetFunctor J phi k where
  app F := comparison J phi F k
  naturality _ _ f := comparison_naturality J phi k f

/-- The natural transformation whose components are the explicit inverse principal-parts
sheafification comparisons. -/
@[stacks 09CV "inverse natural comparison", stacks 0G3U "inverse natural comparison"]
noncomputable def invNatTrans (phi : O₁ ⟶ O₂) (k : ℕ) :
    targetFunctor J phi k ⟶ sourceFunctor J phi k where
  app F := comparisonInv J phi F k
  naturality _ _ f := comparisonInv_naturality J phi k f

/-- A component of the natural comparison is the objectwise principal-parts comparison. -/
@[simp, stacks 09CV "natural comparison component",
  stacks 0G3U "natural comparison component"]
theorem comparisonNatTrans_app (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    (comparisonNatTrans J phi k).app F = comparison J phi F k := sorry

/-- A component of the inverse natural comparison is the explicit objectwise universal
descent comparison. -/
@[simp, stacks 09CV "inverse natural comparison component",
  stacks 0G3U "inverse natural comparison component"]
theorem invNatTrans_app (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    (invNatTrans J phi k).app F = comparisonInv J phi F k := sorry

/-- The natural comparison followed by the inverse natural comparison is the identity. -/
@[simp, stacks 09CV "natural comparison forward-inverse law",
  stacks 0G3U "natural comparison forward-inverse law"]
theorem comparisonNatTrans_hom_inv_id (phi : O₁ ⟶ O₂) (k : ℕ) :
    comparisonNatTrans J phi k ≫ invNatTrans J phi k = 𝟙 _ := sorry

/-- The inverse natural comparison followed by the forward natural comparison is the
identity. -/
@[simp, stacks 09CV "natural comparison inverse-forward law",
  stacks 0G3U "natural comparison inverse-forward law"]
theorem comparisonNatTrans_inv_hom_id (phi : O₁ ⟶ O₂) (k : ℕ) :
    invNatTrans J phi k ≫ comparisonNatTrans J phi k = 𝟙 _ := sorry

/-- Principal-parts formation commutes naturally with sheafification. -/
@[stacks 09CV "natural comparison isomorphism",
  stacks 0G3U "natural comparison isomorphism"]
noncomputable def comparisonNatIso (phi : O₁ ⟶ O₂) (k : ℕ) :
    sourceFunctor J phi k ≅ targetFunctor J phi k where
  hom := comparisonNatTrans J phi k
  inv := invNatTrans J phi k
  hom_inv_id := comparisonNatTrans_hom_inv_id J phi k
  inv_hom_id := comparisonNatTrans_inv_hom_id J phi k

/-- A component of the natural comparison is the objectwise principal-parts comparison. -/
@[simp, stacks 09CV "natural comparison isomorphism component",
  stacks 0G3U "natural comparison isomorphism component"]
theorem comparisonNatIso_app (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    (comparisonNatIso J phi k).app F = comparisonIso J phi F k := sorry

/-- The forward natural transformation of `comparisonNatIso` is the explicit comparison. -/
@[simp, stacks 09CV "natural comparison isomorphism hom",
  stacks 0G3U "natural comparison isomorphism hom"]
theorem comparisonNatIso_hom (phi : O₁ ⟶ O₂) (k : ℕ) :
    (comparisonNatIso J phi k).hom = comparisonNatTrans J phi k := sorry

/-- The inverse natural transformation of `comparisonNatIso` is the explicit inverse
comparison transformation. -/
@[simp, stacks 09CV "natural comparison isomorphism inverse",
  stacks 0G3U "natural comparison isomorphism inverse"]
theorem comparisonNatIso_inv (phi : O₁ ⟶ O₂) (k : ℕ) :
    (comparisonNatIso J phi k).inv = invNatTrans J phi k := sorry

/-- The forward component of `comparisonNatIso` is the objectwise comparison morphism. -/
@[simp, stacks 09CV "natural comparison isomorphism hom component",
  stacks 0G3U "natural comparison isomorphism hom component"]
theorem comparisonNatIso_hom_app (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    (comparisonNatIso J phi k).hom.app F = comparison J phi F k := sorry

/-- The inverse component of `comparisonNatIso` is the explicit objectwise universal descent
comparison. -/
@[stacks 09CV "inverse natural comparison component",
  stacks 0G3U "inverse natural comparison component", simp]
theorem comparisonNatIso_inv_app (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ) :
    (comparisonNatIso J phi k).inv.app F = comparisonInv J phi F k := sorry

end SheafOfModules.RingedSite.PrincipalParts.Sheafification
