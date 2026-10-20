/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Groupoid.InFunctors.Iso
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Representability of groupoids in functors

Coyoneda presentations with an existing pushout and the isomorphism-invariant
representability property of a groupoid in functors.
-/

@[expose] public section

open CategoryTheory Limits Opposite

noncomputable section

universe u v

namespace CategoryTheory.GroupoidInFunctors

variable {C : Type u} [Category.{v} C]

/-- The evaluated pullback projections give a compatible pair of morphisms out of `R`. -/
private theorem pullbackCoyonedaHomApp_condition {objU objR : C}
    (src tgt : objU ⟶ objR) [HasPushout src tgt] (T : C)
    (x : (pullback (coyoneda.map (op src)) (coyoneda.map (op tgt))).obj T) :
    src ≫
        pullback.fst ((coyoneda.map (op src)).app T) ((coyoneda.map (op tgt)).app T)
          ((pullbackObjIso (coyoneda.map (op src)) (coyoneda.map (op tgt)) T).hom x) =
      tgt ≫
        pullback.snd ((coyoneda.map (op src)).app T) ((coyoneda.map (op tgt)).app T)
          ((pullbackObjIso (coyoneda.map (op src)) (coyoneda.map (op tgt)) T).hom x) := sorry

/-- The `T`-component of the coyoneda comparison out of the functor-level pullback. -/
def pullbackCoyonedaHomApp {objU objR : C} (src tgt : objU ⟶ objR) [HasPushout src tgt]
    (T : C) :
    (pullback (coyoneda.map (op src)) (coyoneda.map (op tgt))).obj T ⟶
      (coyoneda.obj (op (pushout src tgt))).obj T :=
  ↾fun x ↦
    pushout.desc
      (pullback.fst ((coyoneda.map (op src)).app T) ((coyoneda.map (op tgt)).app T)
        ((pullbackObjIso (coyoneda.map (op src)) (coyoneda.map (op tgt)) T).hom x))
      (pullback.snd ((coyoneda.map (op src)).app T) ((coyoneda.map (op tgt)).app T)
        ((pullbackObjIso (coyoneda.map (op src)) (coyoneda.map (op tgt)) T).hom x))
      (by exact pullbackCoyonedaHomApp_condition src tgt T x)

/-- Precomposition with the pushout inclusions gives a compatible pair of arrows. -/
private theorem pullbackCoyonedaInvApp_condition {objU objR : C}
    (src tgt : objU ⟶ objR) [HasPushout src tgt] (T : C) (h : pushout src tgt ⟶ T) :
    (coyoneda.map (op src)).app T (pushout.inl src tgt ≫ h) =
      (coyoneda.map (op tgt)).app T (pushout.inr src tgt ≫ h) := sorry

/-- The `T`-component of the coyoneda comparison into the functor-level pullback. -/
def pullbackCoyonedaInvApp {objU objR : C} (src tgt : objU ⟶ objR) [HasPushout src tgt]
    (T : C) :
    (coyoneda.obj (op (pushout src tgt))).obj T ⟶
      (pullback (coyoneda.map (op src)) (coyoneda.map (op tgt))).obj T :=
  ↾fun h ↦
    (pullbackObjIso (coyoneda.map (op src)) (coyoneda.map (op tgt)) T).inv
      ((Types.pullbackIsoPullback
          ((coyoneda.map (op src)).app T) ((coyoneda.map (op tgt)).app T)).inv
        ⟨⟨pushout.inl src tgt ≫ h, pushout.inr src tgt ≫ h⟩,
          by exact pullbackCoyonedaInvApp_condition src tgt T h⟩)

/-- The forward coyoneda comparison commutes with transitions in the base category. -/
private theorem pullbackCoyonedaHomApp_naturality {objU objR : C}
    (src tgt : objU ⟶ objR) [HasPushout src tgt] {T T' : C} (f : T ⟶ T') :
    (pullback (coyoneda.map (op src)) (coyoneda.map (op tgt))).map f ≫
        pullbackCoyonedaHomApp src tgt T' =
      pullbackCoyonedaHomApp src tgt T ≫ (coyoneda.obj (op (pushout src tgt))).map f := sorry

/-- The reverse coyoneda comparison commutes with transitions in the base category. -/
private theorem pullbackCoyonedaInvApp_naturality {objU objR : C}
    (src tgt : objU ⟶ objR) [HasPushout src tgt] {T T' : C} (f : T ⟶ T') :
    (coyoneda.obj (op (pushout src tgt))).map f ≫ pullbackCoyonedaInvApp src tgt T' =
      pullbackCoyonedaInvApp src tgt T ≫
        (pullback (coyoneda.map (op src)) (coyoneda.map (op tgt))).map f := sorry

/-- The forward comparison followed by the reverse comparison is the identity at each object. -/
private theorem pullbackCoyonedaHomApp_inv {objU objR : C}
    (src tgt : objU ⟶ objR) [HasPushout src tgt] (T : C) :
    pullbackCoyonedaHomApp src tgt T ≫ pullbackCoyonedaInvApp src tgt T =
      𝟙 ((pullback (coyoneda.map (op src)) (coyoneda.map (op tgt))).obj T) := sorry

/-- The reverse comparison followed by the forward comparison is the identity at each object. -/
private theorem pullbackCoyonedaInvApp_hom {objU objR : C}
    (src tgt : objU ⟶ objR) [HasPushout src tgt] (T : C) :
    pullbackCoyonedaInvApp src tgt T ≫ pullbackCoyonedaHomApp src tgt T =
      𝟙 ((coyoneda.obj (op (pushout src tgt))).obj T) := sorry

/-- The fibre product of coyoneda source and target maps is corepresented by the pushout. -/
def pullbackCoyonedaIso {objU objR : C} (src tgt : objU ⟶ objR) [HasPushout src tgt] :
    pullback (coyoneda.map (op src)) (coyoneda.map (op tgt)) ≅
      coyoneda.obj (op (pushout src tgt)) where
  hom :=
    { app := pullbackCoyonedaHomApp src tgt
      naturality := by
        intro T T' f
        exact pullbackCoyonedaHomApp_naturality src tgt f }
  inv :=
    { app := pullbackCoyonedaInvApp src tgt
      naturality := by
        intro T T' f
        exact pullbackCoyonedaInvApp_naturality src tgt f }
  hom_inv_id := by
    apply NatTrans.ext
    funext T
    exact pullbackCoyonedaHomApp_inv src tgt T
  inv_hom_id := by
    apply NatTrans.ext
    funext T
    exact pullbackCoyonedaInvApp_hom src tgt T

/-- The forward comparison is given objectwise by `pullbackCoyonedaHomApp`. -/
theorem pullbackCoyonedaIso_hom_app {objU objR : C} (src tgt : objU ⟶ objR)
    [HasPushout src tgt] (T : C) :
    (pullbackCoyonedaIso src tgt).hom.app T = pullbackCoyonedaHomApp src tgt T :=
  rfl

/-- The reverse comparison is given objectwise by `pullbackCoyonedaInvApp`. -/
theorem pullbackCoyonedaIso_inv_app {objU objR : C} (src tgt : objU ⟶ objR)
    [HasPushout src tgt] (T : C) :
    (pullbackCoyonedaIso src tgt).inv.app T = pullbackCoyonedaInvApp src tgt T :=
  rfl

/-- Functor-level composition of a coyoneda presentation, via the pushout comparison. -/
def coyonedaComp {objU objR : C} (src tgt : objU ⟶ objR) [HasPushout src tgt]
    (comp : objR ⟶ pushout src tgt) :
    pullback (coyoneda.map (op src)) (coyoneda.map (op tgt)) ⟶ coyoneda.obj (op objR) :=
  (pullbackCoyonedaIso src tgt).hom ≫ coyoneda.map (op comp)

/-- Unfolding of functor-level coyoneda composition. -/
theorem coyonedaComp_def {objU objR : C} (src tgt : objU ⟶ objR) [HasPushout src tgt]
    (comp : objR ⟶ pushout src tgt) :
    coyonedaComp src tgt comp =
      (pullbackCoyonedaIso src tgt).hom ≫ coyoneda.map (op comp) :=
  rfl

/-- Morphisms into the pushout correspond bijectively to natural transformations from
the pullback of the coyoneda source and target maps to the arrow functor. -/
theorem coyonedaComp_bijective {U R : C} (s t : U ⟶ R) [HasPushout s t] :
    Function.Bijective (coyonedaComp s t) :=
  sorry

/-- Every natural transformation from the coyoneda pullback to the arrow functor is
induced by a unique morphism into the pushout. -/
theorem existsUnique_coyonedaComp {U R : C} (s t : U ⟶ R) [HasPushout s t]
    (cFun : pullback (coyoneda.map (op s)) (coyoneda.map (op t)) ⟶ coyoneda.obj (op R)) :
    ∃! c : R ⟶ pushout s t, coyonedaComp s t c = cFun :=
  sorry

/-- The groupoid-in-functors laws on a coyoneda quintuple, including the unique identity
and inverse maps required by the bundled carrier. -/
structure CoyonedaGroupoidLaws {objU objR : C} (src tgt : objU ⟶ objR)
    [HasPushout src tgt] (comp : objR ⟶ pushout src tgt)
    (idMap : coyoneda.obj (op objU) ⟶ coyoneda.obj (op objR))
    (invMap : coyoneda.obj (op objR) ⟶ coyoneda.obj (op objR)) : Prop where
  /-- The source of a composite is the source of the earlier arrow. -/
  comp_source :
    coyonedaComp src tgt comp ≫ coyoneda.map (op src) =
      pullback.snd (coyoneda.map (op src)) (coyoneda.map (op tgt)) ≫ coyoneda.map (op src)
  /-- The target of a composite is the target of the later arrow. -/
  comp_target :
    coyonedaComp src tgt comp ≫ coyoneda.map (op tgt) =
      pullback.fst (coyoneda.map (op src)) (coyoneda.map (op tgt)) ≫ coyoneda.map (op tgt)
  /-- Identity arrows have the specified source. -/
  identity_source : idMap ≫ coyoneda.map (op src) = 𝟙 (coyoneda.obj (op objU))
  /-- Identity arrows have the specified target. -/
  identity_target : idMap ≫ coyoneda.map (op tgt) = 𝟙 (coyoneda.obj (op objU))
  /-- Inversion exchanges source with target. -/
  inverse_source : invMap ≫ coyoneda.map (op src) = coyoneda.map (op tgt)
  /-- Inversion exchanges target with source. -/
  inverse_target : invMap ≫ coyoneda.map (op tgt) = coyoneda.map (op src)
  /-- Composition is associative on generalized arrows. -/
  associativity :
    ∀ {W : C ⥤ Type v} (a b d : W ⟶ coyoneda.obj (op objR))
      (h_ab : a ≫ coyoneda.map (op src) = b ≫ coyoneda.map (op tgt))
      (h_bd : b ≫ coyoneda.map (op src) = d ≫ coyoneda.map (op tgt))
      (h_ab_d :
        (pullback.lift a b h_ab ≫ coyonedaComp src tgt comp) ≫ coyoneda.map (op src) =
          d ≫ coyoneda.map (op tgt))
      (h_a_bd :
        a ≫ coyoneda.map (op src) =
          (pullback.lift b d h_bd ≫ coyonedaComp src tgt comp) ≫ coyoneda.map (op tgt)),
      pullback.lift (pullback.lift a b h_ab ≫ coyonedaComp src tgt comp) d h_ab_d ≫
          coyonedaComp src tgt comp =
        pullback.lift a (pullback.lift b d h_bd ≫ coyonedaComp src tgt comp) h_a_bd ≫
          coyonedaComp src tgt comp
  /-- Composing an arrow with the identity at its source does not change it. -/
  right_identity :
    ∀ {W : C ⥤ Type v} (a : W ⟶ coyoneda.obj (op objR))
      (h :
        a ≫ coyoneda.map (op src) =
          ((a ≫ coyoneda.map (op src)) ≫ idMap) ≫ coyoneda.map (op tgt)),
      pullback.lift a ((a ≫ coyoneda.map (op src)) ≫ idMap) h ≫ coyonedaComp src tgt comp = a
  /-- Composing the identity at the target of an arrow with that arrow does not change it. -/
  left_identity :
    ∀ {W : C ⥤ Type v} (a : W ⟶ coyoneda.obj (op objR))
      (h :
        ((a ≫ coyoneda.map (op tgt)) ≫ idMap) ≫ coyoneda.map (op src) =
          a ≫ coyoneda.map (op tgt)),
      pullback.lift ((a ≫ coyoneda.map (op tgt)) ≫ idMap) a h ≫ coyonedaComp src tgt comp = a
  /-- Composing an arrow after its inverse gives the identity at its target. -/
  inverse_comp :
    ∀ {W : C ⥤ Type v} (a : W ⟶ coyoneda.obj (op objR))
      (h : a ≫ coyoneda.map (op src) = (a ≫ invMap) ≫ coyoneda.map (op tgt)),
      pullback.lift a (a ≫ invMap) h ≫ coyonedaComp src tgt comp =
        (a ≫ coyoneda.map (op tgt)) ≫ idMap
  /-- Composing the inverse of an arrow after it gives the identity at its source. -/
  comp_inverse :
    ∀ {W : C ⥤ Type v} (a : W ⟶ coyoneda.obj (op objR))
      (h : (a ≫ invMap) ≫ coyoneda.map (op src) = a ≫ coyoneda.map (op tgt)),
      pullback.lift (a ≫ invMap) a h ≫ coyonedaComp src tgt comp =
        (a ≫ coyoneda.map (op src)) ≫ idMap

/-- Package the coyoneda groupoid laws from their individual components. -/
theorem CoyonedaGroupoidLaws.of {objU objR : C} (src tgt : objU ⟶ objR) [HasPushout src tgt]
    (comp : objR ⟶ pushout src tgt)
    (idMap : coyoneda.obj (op objU) ⟶ coyoneda.obj (op objR))
    (invMap : coyoneda.obj (op objR) ⟶ coyoneda.obj (op objR))
    (comp_source :
      coyonedaComp src tgt comp ≫ coyoneda.map (op src) =
        pullback.snd (coyoneda.map (op src)) (coyoneda.map (op tgt)) ≫ coyoneda.map (op src))
    (comp_target :
      coyonedaComp src tgt comp ≫ coyoneda.map (op tgt) =
        pullback.fst (coyoneda.map (op src)) (coyoneda.map (op tgt)) ≫ coyoneda.map (op tgt))
    (identity_source : idMap ≫ coyoneda.map (op src) = 𝟙 (coyoneda.obj (op objU)))
    (identity_target : idMap ≫ coyoneda.map (op tgt) = 𝟙 (coyoneda.obj (op objU)))
    (inverse_source : invMap ≫ coyoneda.map (op src) = coyoneda.map (op tgt))
    (inverse_target : invMap ≫ coyoneda.map (op tgt) = coyoneda.map (op src))
    (associativity :
      ∀ {W : C ⥤ Type v} (a b d : W ⟶ coyoneda.obj (op objR))
        (h_ab : a ≫ coyoneda.map (op src) = b ≫ coyoneda.map (op tgt))
        (h_bd : b ≫ coyoneda.map (op src) = d ≫ coyoneda.map (op tgt))
        (h_ab_d :
          (pullback.lift a b h_ab ≫ coyonedaComp src tgt comp) ≫ coyoneda.map (op src) =
            d ≫ coyoneda.map (op tgt))
        (h_a_bd :
          a ≫ coyoneda.map (op src) =
            (pullback.lift b d h_bd ≫ coyonedaComp src tgt comp) ≫ coyoneda.map (op tgt)),
        pullback.lift (pullback.lift a b h_ab ≫ coyonedaComp src tgt comp) d h_ab_d ≫
            coyonedaComp src tgt comp =
          pullback.lift a (pullback.lift b d h_bd ≫ coyonedaComp src tgt comp) h_a_bd ≫
            coyonedaComp src tgt comp)
    (right_identity :
      ∀ {W : C ⥤ Type v} (a : W ⟶ coyoneda.obj (op objR))
        (h :
          a ≫ coyoneda.map (op src) =
            ((a ≫ coyoneda.map (op src)) ≫ idMap) ≫ coyoneda.map (op tgt)),
        pullback.lift a ((a ≫ coyoneda.map (op src)) ≫ idMap) h ≫
          coyonedaComp src tgt comp = a)
    (left_identity :
      ∀ {W : C ⥤ Type v} (a : W ⟶ coyoneda.obj (op objR))
        (h :
          ((a ≫ coyoneda.map (op tgt)) ≫ idMap) ≫ coyoneda.map (op src) =
            a ≫ coyoneda.map (op tgt)),
        pullback.lift ((a ≫ coyoneda.map (op tgt)) ≫ idMap) a h ≫
          coyonedaComp src tgt comp = a)
    (inverse_comp :
      ∀ {W : C ⥤ Type v} (a : W ⟶ coyoneda.obj (op objR))
        (h : a ≫ coyoneda.map (op src) = (a ≫ invMap) ≫ coyoneda.map (op tgt)),
        pullback.lift a (a ≫ invMap) h ≫ coyonedaComp src tgt comp =
          (a ≫ coyoneda.map (op tgt)) ≫ idMap)
    (comp_inverse :
      ∀ {W : C ⥤ Type v} (a : W ⟶ coyoneda.obj (op objR))
        (h : (a ≫ invMap) ≫ coyoneda.map (op src) = a ≫ coyoneda.map (op tgt)),
        pullback.lift (a ≫ invMap) a h ≫ coyonedaComp src tgt comp =
          (a ≫ coyoneda.map (op src)) ≫ idMap) :
    CoyonedaGroupoidLaws src tgt comp idMap invMap where
  comp_source := comp_source
  comp_target := comp_target
  identity_source := identity_source
  identity_target := identity_target
  inverse_source := inverse_source
  inverse_target := inverse_target
  associativity := associativity
  right_identity := right_identity
  left_identity := left_identity
  inverse_comp := inverse_comp
  comp_inverse := comp_inverse

/-- The packaged coyoneda laws recover source, target, identity, and inverse compatibilities. -/
theorem CoyonedaGroupoidLaws.spec {objU objR : C} {src tgt : objU ⟶ objR}
    [HasPushout src tgt] {comp : objR ⟶ pushout src tgt}
    {idMap : coyoneda.obj (op objU) ⟶ coyoneda.obj (op objR)}
    {invMap : coyoneda.obj (op objR) ⟶ coyoneda.obj (op objR)}
    (laws : CoyonedaGroupoidLaws src tgt comp idMap invMap) :
    (coyonedaComp src tgt comp ≫ coyoneda.map (op src) =
        pullback.snd (coyoneda.map (op src)) (coyoneda.map (op tgt)) ≫
          coyoneda.map (op src)) ∧
      (coyonedaComp src tgt comp ≫ coyoneda.map (op tgt) =
        pullback.fst (coyoneda.map (op src)) (coyoneda.map (op tgt)) ≫
          coyoneda.map (op tgt)) ∧
      (idMap ≫ coyoneda.map (op src) = 𝟙 (coyoneda.obj (op objU))) ∧
      (idMap ≫ coyoneda.map (op tgt) = 𝟙 (coyoneda.obj (op objU))) ∧
      (invMap ≫ coyoneda.map (op src) = coyoneda.map (op tgt)) ∧
      (invMap ≫ coyoneda.map (op tgt) = coyoneda.map (op src)) :=
  ⟨laws.comp_source, laws.comp_target, laws.identity_source, laws.identity_target,
    laws.inverse_source, laws.inverse_target⟩

/-- The coyoneda form of a groupoid in functors, presented by morphisms `src, tgt : U ⟶ R`
in `C`, a composition morphism into the pushout, and proofs that the induced quintuple
satisfies the groupoid-in-functors laws. -/
def ofCoyoneda {objU objR : C} (src tgt : objU ⟶ objR) [HasPushout src tgt]
    (comp : objR ⟶ pushout src tgt)
    (idMap : coyoneda.obj (op objU) ⟶ coyoneda.obj (op objR))
    (invMap : coyoneda.obj (op objR) ⟶ coyoneda.obj (op objR))
    (laws : CoyonedaGroupoidLaws src tgt comp idMap invMap) :
    GroupoidInFunctors.{u, v, v} C where
  U := coyoneda.obj (op objU)
  R := coyoneda.obj (op objR)
  s := coyoneda.map (op src)
  t := coyoneda.map (op tgt)
  c := coyonedaComp src tgt comp
  e := idMap
  i := invMap
  comp_source := laws.comp_source
  comp_target := laws.comp_target
  identity_source := laws.identity_source
  identity_target := laws.identity_target
  inverse_source := laws.inverse_source
  inverse_target := laws.inverse_target
  associativity := laws.associativity
  right_identity := laws.right_identity
  left_identity := laws.left_identity
  inverse_comp := laws.inverse_comp
  comp_inverse := laws.comp_inverse

/-- The object functor of a coyoneda presentation is `coyoneda.obj (op U)`. -/
theorem ofCoyoneda_U {objU objR : C} (src tgt : objU ⟶ objR) [HasPushout src tgt]
    (comp : objR ⟶ pushout src tgt)
    (idMap : coyoneda.obj (op objU) ⟶ coyoneda.obj (op objR))
    (invMap : coyoneda.obj (op objR) ⟶ coyoneda.obj (op objR))
    (laws : CoyonedaGroupoidLaws src tgt comp idMap invMap) :
    (ofCoyoneda src tgt comp idMap invMap laws).U = coyoneda.obj (op objU) := rfl

/-- The arrow functor of a coyoneda presentation is `coyoneda.obj (op R)`. -/
theorem ofCoyoneda_R {objU objR : C} (src tgt : objU ⟶ objR) [HasPushout src tgt]
    (comp : objR ⟶ pushout src tgt)
    (idMap : coyoneda.obj (op objU) ⟶ coyoneda.obj (op objR))
    (invMap : coyoneda.obj (op objR) ⟶ coyoneda.obj (op objR))
    (laws : CoyonedaGroupoidLaws src tgt comp idMap invMap) :
    (ofCoyoneda src tgt comp idMap invMap laws).R = coyoneda.obj (op objR) := rfl

/-- The source transformation of a coyoneda presentation is precomposition with `src`. -/
theorem ofCoyoneda_s {objU objR : C} (src tgt : objU ⟶ objR) [HasPushout src tgt]
    (comp : objR ⟶ pushout src tgt)
    (idMap : coyoneda.obj (op objU) ⟶ coyoneda.obj (op objR))
    (invMap : coyoneda.obj (op objR) ⟶ coyoneda.obj (op objR))
    (laws : CoyonedaGroupoidLaws src tgt comp idMap invMap) :
    (ofCoyoneda src tgt comp idMap invMap laws).s = coyoneda.map (op src) := rfl

/-- The target transformation of a coyoneda presentation is precomposition with `tgt`. -/
theorem ofCoyoneda_t {objU objR : C} (src tgt : objU ⟶ objR) [HasPushout src tgt]
    (comp : objR ⟶ pushout src tgt)
    (idMap : coyoneda.obj (op objU) ⟶ coyoneda.obj (op objR))
    (invMap : coyoneda.obj (op objR) ⟶ coyoneda.obj (op objR))
    (laws : CoyonedaGroupoidLaws src tgt comp idMap invMap) :
    (ofCoyoneda src tgt comp idMap invMap laws).t = coyoneda.map (op tgt) := rfl

/-- The composition of a coyoneda presentation is `coyonedaComp src tgt comp`. -/
theorem ofCoyoneda_c {objU objR : C} (src tgt : objU ⟶ objR) [HasPushout src tgt]
    (comp : objR ⟶ pushout src tgt)
    (idMap : coyoneda.obj (op objU) ⟶ coyoneda.obj (op objR))
    (invMap : coyoneda.obj (op objR) ⟶ coyoneda.obj (op objR))
    (laws : CoyonedaGroupoidLaws src tgt comp idMap invMap) :
    (ofCoyoneda src tgt comp idMap invMap laws).c = coyonedaComp src tgt comp := rfl

/-- The identity map of a coyoneda presentation is the supplied identity transformation. -/
theorem ofCoyoneda_e {objU objR : C} (src tgt : objU ⟶ objR) [HasPushout src tgt]
    (comp : objR ⟶ pushout src tgt)
    (idMap : coyoneda.obj (op objU) ⟶ coyoneda.obj (op objR))
    (invMap : coyoneda.obj (op objR) ⟶ coyoneda.obj (op objR))
    (laws : CoyonedaGroupoidLaws src tgt comp idMap invMap) :
    (ofCoyoneda src tgt comp idMap invMap laws).e = idMap := rfl

/-- The inverse map of a coyoneda presentation is the supplied inverse transformation. -/
theorem ofCoyoneda_i {objU objR : C} (src tgt : objU ⟶ objR) [HasPushout src tgt]
    (comp : objR ⟶ pushout src tgt)
    (idMap : coyoneda.obj (op objU) ⟶ coyoneda.obj (op objR))
    (invMap : coyoneda.obj (op objR) ⟶ coyoneda.obj (op objR))
    (laws : CoyonedaGroupoidLaws src tgt comp idMap invMap) :
    (ofCoyoneda src tgt comp idMap invMap laws).i = invMap := rfl

/-- A groupoid in functors on `C` is representable if it is isomorphic to a coyoneda
form `(coyoneda.obj (op U), coyoneda.obj (op R), s, t, c)` for objects `U`, `R` of `C`
such that the pushout of the corresponding morphisms `U ⟶ R` exists and the coyoneda
quintuple satisfies the groupoid-in-functors laws. -/
class IsRepresentable (G : GroupoidInFunctors.{u, v, v} C) : Prop where
  /-- There exist representing objects, source/target morphisms whose pushout exists,
  a composition morphism, identity and inverse maps, and groupoid laws, with an
  isomorphism to the corresponding coyoneda presentation. -/
  exists_representation :
    ∃ (objU objR : C) (src tgt : objU ⟶ objR) (h : HasPushout src tgt)
      (comp : objR ⟶ @pushout C _ objU objR objR src tgt h)
      (idMap : coyoneda.obj (op objU) ⟶ coyoneda.obj (op objR))
      (invMap : coyoneda.obj (op objR) ⟶ coyoneda.obj (op objR))
      (laws : @CoyonedaGroupoidLaws C _ objU objR src tgt h comp idMap invMap),
      Nonempty (Iso (@ofCoyoneda C _ objU objR src tgt h comp idMap invMap laws) G)

/-- A coyoneda presentation satisfying the groupoid laws is representable. -/
theorem isRepresentable_ofCoyoneda {objU objR : C} (src tgt : objU ⟶ objR)
    [HasPushout src tgt] (comp : objR ⟶ pushout src tgt)
    (idMap : coyoneda.obj (op objU) ⟶ coyoneda.obj (op objR))
    (invMap : coyoneda.obj (op objR) ⟶ coyoneda.obj (op objR))
    (laws : CoyonedaGroupoidLaws src tgt comp idMap invMap) :
    IsRepresentable (ofCoyoneda src tgt comp idMap invMap laws) where
  exists_representation :=
    ⟨objU, objR, src, tgt, inferInstance, comp, idMap, invMap, laws,
      ⟨Iso.refl (ofCoyoneda src tgt comp idMap invMap laws)⟩⟩

/-- Representability is equivalent to existence of a coyoneda presentation with existing
pushout, identity and inverse maps, groupoid laws, and an isomorphism to that presentation. -/
theorem isRepresentable_iff (G : GroupoidInFunctors.{u, v, v} C) :
    IsRepresentable G ↔
      ∃ (objU objR : C) (src tgt : objU ⟶ objR) (h : HasPushout src tgt)
        (comp : objR ⟶ @pushout C _ objU objR objR src tgt h)
        (idMap : coyoneda.obj (op objU) ⟶ coyoneda.obj (op objR))
        (invMap : coyoneda.obj (op objR) ⟶ coyoneda.obj (op objR))
        (laws : @CoyonedaGroupoidLaws C _ objU objR src tgt h comp idMap invMap),
        Nonempty (Iso (@ofCoyoneda C _ objU objR src tgt h comp idMap invMap laws) G) :=
  ⟨fun h ↦ h.exists_representation, fun h ↦ ⟨h⟩⟩

/-- The object functor of a representable groupoid in functors is corepresentable. -/
theorem isCorepresentable_obj (G : GroupoidInFunctors.{u, v, v} C) [IsRepresentable G] :
    G.U.IsCorepresentable := sorry

/-- The arrow functor of a representable groupoid in functors is corepresentable. -/
theorem isCorepresentable_arrow (G : GroupoidInFunctors.{u, v, v} C)
    [IsRepresentable G] : G.R.IsCorepresentable := sorry

/-- Representability is invariant under isomorphism of groupoids in functors. -/
theorem isRepresentable_of_iso {G H : GroupoidInFunctors.{u, v, v} C} (e : Iso G H)
    [IsRepresentable G] : IsRepresentable H := sorry

end CategoryTheory.GroupoidInFunctors
