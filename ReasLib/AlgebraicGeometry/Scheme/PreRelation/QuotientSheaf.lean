module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientPresheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Sheafification

/-!
# Quotient sheaves of scheme pre-relations

This module sheafifies the objectwise quotient presheaf of a scheme pre-relation and records
its canonical quotient map and comparison with the kernel pair.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- The Type-valued sheafification of a pre-relation's quotient presheaf on the big étale site. -/
noncomputable def smallEtaleQuotientSheaf {S : Scheme.{u}} {U : Over S} (P : PreRelation U) :
    Sheaf (Scheme.etaleTopology.over S) (Type u) :=
  ⟨EtaleSheafification.sheafify P.quotientPresheaf,
    EtaleSheafification.isSheaf P.quotientPresheaf⟩

/-- The canonical map from the quotient presheaf to its Type-valued étale sheafification. -/
noncomputable def toSmallEtaleQuotientSheaf {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) : P.quotientPresheaf ⟶ P.smallEtaleQuotientSheaf.obj :=
  EtaleSheafification.toSheafify P.quotientPresheaf

/-- The quotient projection into the Type-valued étale sheafification. -/
noncomputable def smallEtaleQuotientSheafMk {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) : yoneda.obj U ⟶ P.smallEtaleQuotientSheaf.obj :=
  P.quotientMk ≫ P.toSmallEtaleQuotientSheaf

/-- The Type-valued quotient sheaf satisfies étale descent. -/
theorem smallEtaleQuotientSheaf_isSheaf {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) :
    Presheaf.IsSheaf (Scheme.etaleTopology.over S) P.smallEtaleQuotientSheaf.obj :=
  P.smallEtaleQuotientSheaf.property

/-- The Type-valued quotient sheaf has the universal property of étale sheafification. -/
theorem smallEtaleQuotientSheaf_universal {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) (G : Sheaf (Scheme.etaleTopology.over S) (Type u))
    (η : P.quotientPresheaf ⟶ G.obj) :
    ∃! θ : P.smallEtaleQuotientSheaf.obj ⟶ G.obj,
      P.toSmallEtaleQuotientSheaf ≫ θ = η :=
  EtaleSheafification.universal P.quotientPresheaf G η

/-- The quotient sheaf of a scheme pre-relation for a Grothendieck topology on schemes over the
base. Its values are raised one universe before sheafification. -/
noncomputable def quotientSheaf {S : Scheme.{u}} {U : Over S}
    (J : GrothendieckTopology (Over S)) (P : PreRelation U) :
    Sheaf J (Type (u + 1)) :=
  (presheafToSheaf J (Type (u + 1))).obj
    (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u})

/-- The underlying presheaf of `quotientSheaf` is the sheafification of the universe-raised
quotient presheaf. -/
theorem quotientSheaf_val {S : Scheme.{u}} {U : Over S}
    (J : GrothendieckTopology (Over S)) (P : PreRelation U) :
    (P.quotientSheaf J).obj =
      sheafify J (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u}) := by
  rfl

/-- The section of the quotient sheaf represented by a morphism `a : T ⟶ U`. -/
noncomputable def quotientClass {S : Scheme.{u}} {U T : Over S}
    (J : GrothendieckTopology (Over S)) (P : PreRelation U) (a : T ⟶ U) :
    (P.quotientSheaf J).obj.obj (op T) :=
  (toSheafify J (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u})).app (op T)
    (ULift.up (Quot.mk (P.pointRel T) a))

/-- The quotient class of a point is obtained from the unit of sheafification applied to its
objectwise quotient class. -/
theorem quotientClass_def {S : Scheme.{u}} {U T : Over S}
    (J : GrothendieckTopology (Over S)) (P : PreRelation U) (a : T ⟶ U) :
    P.quotientClass J a =
      (toSheafify J (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u})).app (op T)
        (ULift.up (Quot.mk (P.pointRel T) a)) := by
  rfl

/-- The canonical morphism from the universe-raised representable sheaf of `U` to the quotient
sheaf of `P`. -/
noncomputable def quotientMap {S : Scheme.{u}} {U : Over S}
    (J : GrothendieckTopology (Over S)) [J.Subcanonical] (P : PreRelation U) :
    J.uliftYoneda.{u + 1}.obj U ⟶ P.quotientSheaf J :=
  J.uliftYonedaEquiv.symm (P.quotientClass J (𝟙 U))

/-- Evaluation of the quotient map sends a represented point to its quotient class. -/
theorem quotientMap_app {S : Scheme.{u}} {U T : Over S}
    (J : GrothendieckTopology (Over S)) [J.Subcanonical]
    (P : PreRelation U) (a : T ⟶ U) :
    (P.quotientMap J).hom.app (op T) (ULift.up a) = P.quotientClass J a := by
  have hrepr :
      (P.quotientMap J).hom.app (op T) (ULift.up a) =
        (P.quotientSheaf J).obj.map a.op (P.quotientClass J (𝟙 U)) := by
    simpa [quotientMap] using
      (J.uliftYonedaEquiv_symm_app_apply
        (x := P.quotientClass J (𝟙 U)) (Y := op T) (f := a))
  rw [hrepr, quotientClass_def]
  have hnat :
      (P.quotientSheaf J).obj.map a.op
        ((CategoryTheory.toSheafify J
          (P.quotientPresheaf ⋙ CategoryTheory.uliftFunctor.{u + 1, u})).app (op U)
          (ULift.up (Quot.mk (P.pointRel U) (𝟙 U)))) =
        (CategoryTheory.toSheafify J
          (P.quotientPresheaf ⋙ CategoryTheory.uliftFunctor.{u + 1, u})).app (op T)
          (((P.quotientPresheaf ⋙ CategoryTheory.uliftFunctor.{u + 1, u}).map a.op)
            (ULift.up (Quot.mk (P.pointRel U) (𝟙 U)))) := by
    change (CategoryTheory.sheafify J
        (P.quotientPresheaf ⋙ CategoryTheory.uliftFunctor.{u + 1, u})).map a.op
        ((CategoryTheory.toSheafify J
          (P.quotientPresheaf ⋙ CategoryTheory.uliftFunctor.{u + 1, u})).app (op U)
          (ULift.up (Quot.mk (P.pointRel U) (𝟙 U)))) =
      (CategoryTheory.toSheafify J
        (P.quotientPresheaf ⋙ CategoryTheory.uliftFunctor.{u + 1, u})).app (op T)
        (((P.quotientPresheaf ⋙ CategoryTheory.uliftFunctor.{u + 1, u}).map a.op)
          (ULift.up (Quot.mk (P.pointRel U) (𝟙 U))))
    have hnat := congrArg (fun k => k (ULift.up (Quot.mk (P.pointRel U) (𝟙 U))))
      (((CategoryTheory.toSheafify J
        (P.quotientPresheaf ⋙ CategoryTheory.uliftFunctor.{u + 1, u})).naturality a.op).symm)
    simpa [Category.assoc] using hnat
  rw [hnat]
  have hmap :
      ((P.quotientPresheaf ⋙ CategoryTheory.uliftFunctor.{u + 1, u}).map a.op)
        (ULift.up (Quot.mk (P.pointRel U) (𝟙 U))) =
      ULift.up (Quot.mk (P.pointRel T) a) := by
    change ULift.up (P.quotientPresheaf.map a.op (Quot.mk (P.pointRel U) (𝟙 U))) = _
    rw [P.quotientPresheaf_map_mk]
    rfl
  exact congrArg
    ((CategoryTheory.toSheafify J
      (P.quotientPresheaf ⋙ CategoryTheory.uliftFunctor.{u + 1, u})).app (op T))
    hmap

/-- The quotient map identifies the source and target maps of the pre-relation. -/
theorem quotientMap_s_eq_t {S : Scheme.{u}} {U : Over S}
    (J : GrothendieckTopology (Over S)) [J.Subcanonical] (P : PreRelation U) :
    J.uliftYoneda.{u + 1}.map P.s ≫ P.quotientMap J =
      J.uliftYoneda.{u + 1}.map P.t ≫ P.quotientMap J := by
  apply J.uliftYonedaEquiv.injective
  change (P.quotientMap J).hom.app (op P.left) (ULift.up P.s) =
      (P.quotientMap J).hom.app (op P.left) (ULift.up P.t)
  rw [quotientMap_app, quotientMap_app]
  change
    (CategoryTheory.toSheafify J
      (P.quotientPresheaf ⋙ CategoryTheory.uliftFunctor.{u + 1, u})).app (op P.left)
        (ULift.up (Quot.mk (P.pointRel P.left) P.s)) =
      (CategoryTheory.toSheafify J
        (P.quotientPresheaf ⋙ CategoryTheory.uliftFunctor.{u + 1, u})).app (op P.left)
          (ULift.up (Quot.mk (P.pointRel P.left) P.t))
  have hrel : P.pointRel P.left P.t P.s := by
    rw [P.pointRel_iff]
    exact ⟨𝟙 P.left, by simp, by simp⟩
  have hquot :
      ULift.up (Quot.mk (P.pointRel P.left) P.t) =
        ULift.up (Quot.mk (P.pointRel P.left) P.s) :=
    congrArg ULift.up (Quot.sound hrel)
  exact congrArg
    ((CategoryTheory.toSheafify J
      (P.quotientPresheaf ⋙ CategoryTheory.uliftFunctor.{u + 1, u})).app (op P.left))
    hquot.symm

/-- The represented pre-relation maps canonically to the kernel pair of the quotient map. -/
noncomputable def relationToKernelPair {S : Scheme.{u}} {U : Over S}
    (J : GrothendieckTopology (Over S)) [J.Subcanonical] (P : PreRelation U) :
    J.uliftYoneda.{u + 1}.obj P.left ⟶ pullback (P.quotientMap J) (P.quotientMap J) :=
  pullback.lift (J.uliftYoneda.{u + 1}.map P.s) (J.uliftYoneda.{u + 1}.map P.t)
    (P.quotientMap_s_eq_t J)

/-- The first projection of `relationToKernelPair` is represented by `P.s`. -/
theorem relationToKernelPair_fst {S : Scheme.{u}} {U : Over S}
    (J : GrothendieckTopology (Over S)) [J.Subcanonical] (P : PreRelation U) :
    P.relationToKernelPair J ≫ pullback.fst (P.quotientMap J) (P.quotientMap J) =
      J.uliftYoneda.{u + 1}.map P.s := by
  simpa [relationToKernelPair] using
    (pullback.lift_fst (J.uliftYoneda.{u + 1}.map P.s) (J.uliftYoneda.{u + 1}.map P.t)
      (P.quotientMap_s_eq_t J))

/-- The second projection of `relationToKernelPair` is represented by `P.t`. -/
theorem relationToKernelPair_snd {S : Scheme.{u}} {U : Over S}
    (J : GrothendieckTopology (Over S)) [J.Subcanonical] (P : PreRelation U) :
    P.relationToKernelPair J ≫ pullback.snd (P.quotientMap J) (P.quotientMap J) =
      J.uliftYoneda.{u + 1}.map P.t := by
  simpa [relationToKernelPair] using
    (pullback.lift_snd (J.uliftYoneda.{u + 1}.map P.s) (J.uliftYoneda.{u + 1}.map P.t)
      (P.quotientMap_s_eq_t J))

/-- The sheafification unit commutes with restriction of quotient-presheaf sections. -/
private lemma quotientSheafMap_apply_toSheafify {S : Scheme.{u}} {U T T' : Over S}
    (J : GrothendieckTopology (Over S)) (P : PreRelation U) (f : T' ⟶ T)
    (x : (P.quotientPresheaf ⋙ CategoryTheory.uliftFunctor.{u + 1, u}).obj (op T)) :
    (P.quotientSheaf J).1.map f.op
      ((CategoryTheory.toSheafify J (P.quotientPresheaf ⋙
        CategoryTheory.uliftFunctor.{u + 1, u})).app (op T) x) =
      (CategoryTheory.toSheafify J (P.quotientPresheaf ⋙
        CategoryTheory.uliftFunctor.{u + 1, u})).app (op T')
        (((P.quotientPresheaf ⋙ CategoryTheory.uliftFunctor.{u + 1, u}).map f.op) x) := by
  change (CategoryTheory.sheafify J (P.quotientPresheaf ⋙
      CategoryTheory.uliftFunctor.{u + 1, u})).map f.op
      ((CategoryTheory.toSheafify J (P.quotientPresheaf ⋙
        CategoryTheory.uliftFunctor.{u + 1, u})).app (op T) x) =
    (CategoryTheory.toSheafify J (P.quotientPresheaf ⋙
      CategoryTheory.uliftFunctor.{u + 1, u})).app (op T')
      (((P.quotientPresheaf ⋙ CategoryTheory.uliftFunctor.{u + 1, u}).map f.op) x)
  have hnat := congrArg (fun k => k x)
    (((CategoryTheory.toSheafify J (P.quotientPresheaf ⋙
      CategoryTheory.uliftFunctor.{u + 1, u})).naturality f.op).symm)
  simpa [Category.assoc] using hnat

/-- Restricting a quotient class along a morphism gives the quotient class of the restricted
point. -/
theorem quotientClass_map {S : Scheme.{u}} {U T T' : Over S}
    (J : GrothendieckTopology (Over S)) (P : PreRelation U) (f : T' ⟶ T) (a : T ⟶ U) :
    (P.quotientSheaf J).1.map f.op (P.quotientClass J a) = P.quotientClass J (f ≫ a) := by
  rw [quotientClass_def, quotientClass_def]
  rw [quotientSheafMap_apply_toSheafify J P f]
  have hmap :
      ((P.quotientPresheaf ⋙ CategoryTheory.uliftFunctor.{u + 1, u}).map f.op)
          (ULift.up (Quot.mk (P.pointRel T) a)) =
        ULift.up (Quot.mk (P.pointRel T') (f ≫ a)) := by
    change ULift.up (P.quotientPresheaf.map f.op (Quot.mk (P.pointRel T) a)) = _
    rw [P.quotientPresheaf_map_mk]
    rfl
  exact congrArg
    ((CategoryTheory.toSheafify J (P.quotientPresheaf ⋙
      CategoryTheory.uliftFunctor.{u + 1, u})).app (op T'))
    hmap

end AlgebraicGeometry.Scheme.PreRelation
