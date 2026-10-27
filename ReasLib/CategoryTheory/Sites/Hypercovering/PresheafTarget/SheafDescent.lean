/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Terminal
public import ReasLib.CategoryTheory.Sites.Family.Simplicial.Cartesian

/-!
# Hypercovering descent equivalence for sheaves

If `K` is a hypercovering of the terminal presheaf, then `a⁻¹ : Sh(C) ⥤ Sh((C / K)_total)`
is fully faithful with essential image the cartesian sheaves, and `a_*` is a quasi-inverse.
The same statement holds for abelian sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Functor
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [h_eq : HasEqualizers C] [h_pb : HasPullbacks C]
include h_eq h_pb
variable (K : HypercoveringOf.Terminal.{w} J)
variable (A : Type (max w u v + 1)) [Category.{max w u v} A]
variable [HasWeakSheafify J A]
variable [HasWeakSheafify (overSiteTotalTopology J K.simplicial) A]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify (overSitePrecoverage J K.simplicial n).toGrothendieck A]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify (overSitePrecoverage J K.simplicial n).toGrothendieck
      (Type (max w u v))]
variable [HasWeakSheafify (overSiteTotalTopology J K.simplicial) (Type (max w u v))]
variable [∀ P : (Grothendieck (overSiteDiagram K.simplicial))ᵒᵖ ⥤ A,
    (totalForget K.simplicial).op.HasPointwiseRightKanExtension P]

/-- The adjunction `a⁻¹ ⊣ a_*` presented by the continuous and cocontinuous functor
`j_total`. -/
def sheafLocalizationAdjunction :
    inverseImage J K.simplicial A ⊣ directImage J K.simplicial A :=
  (totalForget K.simplicial).sheafAdjunctionCocontinuous A
    (overSiteTotalTopology J K.simplicial) J

/-- `sheafLocalizationAdjunction` is `sheafAdjunctionCocontinuous` of `j_total`. -/
theorem sheafLocalizationAdjunction_eq :
    sheafLocalizationAdjunction J K A =
      (totalForget K.simplicial).sheafAdjunctionCocontinuous A
        (overSiteTotalTopology J K.simplicial) J :=
  sorry

/-- The functor `a⁻¹` corestricted to cartesian sheaves on `(C / K)_total`. -/
def cartesianFunctor : Sheaf J A ⥤ Cartesian J K.simplicial A :=
  (cartesianProperty J K.simplicial A).lift (inverseImage J K.simplicial A)
    fun F ↦ inverseImage_isCartesian J K.simplicial A F

/-- On objects, `cartesianFunctor` is inverse image along `j_total`. -/
theorem cartesianFunctor_obj (F : Sheaf J A) :
    ((cartesianFunctor J K A).obj F).obj = (inverseImage J K.simplicial A).obj F :=
  sorry

/-- The functor sending a cartesian sheaf on `(C / K)_total` to `a_*` of its underlying
sheaf. -/
def cartesianInverse : Cartesian J K.simplicial A ⥤ Sheaf J A :=
  (cartesianProperty J K.simplicial A).ι ⋙ directImage J K.simplicial A

/-- On objects, `cartesianInverse` is direct image along `j_total`. -/
theorem cartesianInverse_obj (G : Cartesian J K.simplicial A) :
    (cartesianInverse J K A).obj G = (directImage J K.simplicial A).obj G.obj :=
  sorry

/-- Degree-zero local sections of the augmentation extract a family of morphisms from
right-Kan-extension projections. -/
private def descentUnitInvFamily (F : Sheaf J A) (U : C)
    (I : GrothendieckTopology.Cover.Arrow (⟨Presheaf.imageSieve K.zeroMap
      (PUnit.unit : (Presheaf.terminal C).obj (op U)),
      K.zero_locallySurjective.imageSieve_mem _⟩ : J.Cover U)) :
    ((directImage J K.simplicial A).obj ((inverseImage J K.simplicial A).obj F)).obj.obj
        (op U) ⟶ F.obj.obj (op I.Y) :=
  let q := (K.simplicial.obj (op ⦋0⦌)).toPresheafObjEquiv (op I.Y)
    (Presheaf.localPreimage K.zeroMap PUnit.unit I.f I.hf)
  let X : Grothendieck (overSiteDiagram K.simplicial) :=
    ⟨op ⦋0⦌, ⟨q.1, CategoryTheory.Over.mk q.2⟩⟩
  let R := (totalForget K.simplicial).op
  ((RightExtension.mk _ (R.ranCounit.app
    ((inverseImage J K.simplicial A).obj F).obj)).coneAt (op U)).π.app
      (StructuredArrow.mk (Y := op X) I.f.op)

/-- The degree-zero projection family agrees on every overlap of its covering sieve. -/
private theorem descentUnitInvFamily_compatible (F : Sheaf J A) (U : C) :
    ∀ ⦃I₁ I₂ : GrothendieckTopology.Cover.Arrow (⟨Presheaf.imageSieve K.zeroMap
        (PUnit.unit : (Presheaf.terminal C).obj (op U)),
        K.zero_locallySurjective.imageSieve_mem _⟩ : J.Cover U)⦄ (r : I₁.Relation I₂),
      descentUnitInvFamily J K A F U I₁ ≫ F.obj.map r.g₁.op =
        descentUnitInvFamily J K A F U I₂ ≫ F.obj.map r.g₂.op := sorry

/-- Amalgamating degree-zero projections gives the inverse-unit morphism on a sheaf. -/
private def descentUnitInvApp (F : Sheaf J A) :
    (directImage J K.simplicial A).obj ((inverseImage J K.simplicial A).obj F) ⟶ F :=
  ObjectProperty.homMk
    { app := fun U ↦ F.property.amalgamate
        ⟨Presheaf.imageSieve K.zeroMap (PUnit.unit : (Presheaf.terminal C).obj U),
          K.zero_locallySurjective.imageSieve_mem _⟩
        (descentUnitInvFamily J K A F U.unop)
        (descentUnitInvFamily_compatible J K A F U.unop)
      naturality := sorry }

/-- The gluing inverse of the augmentation adjunction unit is natural in the base sheaf. -/
@[no_expose] def descentUnitInv :
    inverseImage J K.simplicial A ⋙ directImage J K.simplicial A ⟶ 𝟭 (Sheaf J A) where
  app := descentUnitInvApp J K A
  naturality := sorry

/-- The gluing inverse and the augmentation unit satisfy both inverse identities. -/
theorem descentUnitInv_spec :
    (sheafLocalizationAdjunction J K A).unit ≫ descentUnitInv J K A = 𝟙 _ ∧
      descentUnitInv J K A ≫ (sheafLocalizationAdjunction J K A).unit = 𝟙 _ := sorry

/-- A local degree-one lift has concrete summand coordinates in its semi-representable family. -/
private def descentCounitLocalPreimage {U : C}
    (t : (pullback K.zeroMap K.zeroMap).obj (op U)) {V : C} (f : V ⟶ U)
    (hf : Presheaf.imageSieve K.oneMap t f) :
    Σ i : (K.simplicial.obj (op ⦋1⦌)).I, V ⟶ (K.simplicial.obj (op ⦋1⦌)).obj i :=
  (K.simplicial.obj (op ⦋1⦌)).toPresheafObjEquiv (op V)
    (Presheaf.localPreimage K.oneMap t f hf)

/-- The first endpoint of a local matching lift has the coordinates of the
restricted first matching projection. -/
private theorem descentCounitLocalPreimage_fst {U : C}
    (t : (pullback K.zeroMap K.zeroMap).obj (op U)) {V : C} (f : V ⟶ U)
    (hf : Presheaf.imageSieve K.oneMap t f) :
    let q := descentCounitLocalPreimage J K t f hf
    (⟨(K.simplicial.δ 0).f q.1, q.2 ≫ (K.simplicial.δ 0).φ q.1⟩ :
      Σ i : (K.simplicial.obj (op ⦋0⦌)).I, V ⟶ (K.simplicial.obj (op ⦋0⦌)).obj i) =
      (K.simplicial.obj (op ⦋0⦌)).toPresheafObjEquiv (op V)
        (((hypercoveringPresheaf K.simplicial).obj (op ⦋0⦌)).map f.op
          ((pullback.fst K.zeroMap K.zeroMap).app (op U) t)) := sorry

/-- The second endpoint of a local matching lift has the coordinates of the
restricted second matching projection. -/
private theorem descentCounitLocalPreimage_snd {U : C}
    (t : (pullback K.zeroMap K.zeroMap).obj (op U)) {V : C} (f : V ⟶ U)
    (hf : Presheaf.imageSieve K.oneMap t f) :
    let q := descentCounitLocalPreimage J K t f hf
    (⟨(K.simplicial.δ 1).f q.1, q.2 ≫ (K.simplicial.δ 1).φ q.1⟩ :
      Σ i : (K.simplicial.obj (op ⦋0⦌)).I, V ⟶ (K.simplicial.obj (op ⦋0⦌)).obj i) =
      (K.simplicial.obj (op ⦋0⦌)).toPresheafObjEquiv (op V)
        (((hypercoveringPresheaf K.simplicial).obj (op ⦋0⦌)).map f.op
          ((pullback.snd K.zeroMap K.zeroMap).app (op U) t)) := sorry

/-- The `δ 0` endpoint of a restricted fixed matching lift is the prescribed
slice object over its first vertex, including the component and structure arrow. -/
private theorem descentCounitLocalPreimage_fst_obj {U : C}
    (x y : Σ i : (K.simplicial.obj (op ⦋0⦌)).I,
      U ⟶ (K.simplicial.obj (op ⦋0⦌)).obj i) :
    let t := (pullbackObjIso K.zeroMap K.zeroMap (op U)).inv
      ((Types.pullbackIsoPullback (K.zeroMap.app (op U)) (K.zeroMap.app (op U))).inv
        ⟨⟨(K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op U) x.1 x.2,
          (K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op U) y.1 y.2⟩,
          @Subsingleton.elim PUnit inferInstance _ _⟩)
    ∀ {V : C} (f : V ⟶ U) (hf : Presheaf.imageSieve K.oneMap t f)
      {W : C} (r : W ⟶ V),
    let q := descentCounitLocalPreimage J K t f hf
    (overMap (K.simplicial.δ 0)).obj ⟨q.1, CategoryTheory.Over.mk (r ≫ q.2)⟩ =
      (⟨x.1, CategoryTheory.Over.mk ((r ≫ f) ≫ x.2)⟩ :
        OverSite (K.simplicial.obj (op ⦋0⦌))) := sorry

/-- The `δ 1` endpoint of a restricted fixed matching lift is the prescribed
slice object over its second vertex, including the component and structure arrow. -/
private theorem descentCounitLocalPreimage_snd_obj {U : C}
    (x y : Σ i : (K.simplicial.obj (op ⦋0⦌)).I,
      U ⟶ (K.simplicial.obj (op ⦋0⦌)).obj i) :
    let t := (pullbackObjIso K.zeroMap K.zeroMap (op U)).inv
      ((Types.pullbackIsoPullback (K.zeroMap.app (op U)) (K.zeroMap.app (op U))).inv
        ⟨⟨(K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op U) x.1 x.2,
          (K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op U) y.1 y.2⟩,
          @Subsingleton.elim PUnit inferInstance _ _⟩)
    ∀ {V : C} (f : V ⟶ U) (hf : Presheaf.imageSieve K.oneMap t f)
      {W : C} (r : W ⟶ V),
    let q := descentCounitLocalPreimage J K t f hf
    (overMap (K.simplicial.δ 1)).obj ⟨q.1, CategoryTheory.Over.mk (r ≫ q.2)⟩ =
      (⟨y.1, CategoryTheory.Over.mk ((r ≫ f) ≫ y.2)⟩ :
        OverSite (K.simplicial.obj (op ⦋0⦌))) := sorry

/-- Equality of dependent endpoint objects gives their canonical transport isomorphism. -/
private def descentCounitEndpointIso {U : C}
    (x y : Σ i : (K.simplicial.obj (op ⦋0⦌)).I,
      U ⟶ (K.simplicial.obj (op ⦋0⦌)).obj i) :
    let t := (pullbackObjIso K.zeroMap K.zeroMap (op U)).inv
      ((Types.pullbackIsoPullback (K.zeroMap.app (op U)) (K.zeroMap.app (op U))).inv
        ⟨⟨(K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op U) x.1 x.2,
          (K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op U) y.1 y.2⟩,
          @Subsingleton.elim PUnit inferInstance _ _⟩)
    ∀ {V : C} (f : V ⟶ U) (hf : Presheaf.imageSieve K.oneMap t f)
      {W : C} (r : W ⟶ V),
    let q := descentCounitLocalPreimage J K t f hf
    ∀ b : Fin 2,
    (overMap (K.simplicial.δ b)).obj ⟨q.1, CategoryTheory.Over.mk (r ≫ q.2)⟩ ≅
      (⟨(if b = 0 then x else y).1,
        CategoryTheory.Over.mk ((r ≫ f) ≫ (if b = 0 then x else y).2)⟩ :
          OverSite (K.simplicial.obj (op ⦋0⦌))) :=
  fun {V} f hf {W} r b ↦ match b with
  | 0 => eqToIso (descentCounitLocalPreimage_fst_obj J K x y f hf r)
  | 1 => eqToIso (descentCounitLocalPreimage_snd_obj J K x y f hf r)

/-- Restricting a fixed matching lift commutes with its endpoint transport isomorphism. -/
private theorem descentCounitEndpointIso_restrict {U : C}
    (x y : Σ i : (K.simplicial.obj (op ⦋0⦌)).I,
      U ⟶ (K.simplicial.obj (op ⦋0⦌)).obj i) :
    let t := (pullbackObjIso K.zeroMap K.zeroMap (op U)).inv
      ((Types.pullbackIsoPullback (K.zeroMap.app (op U)) (K.zeroMap.app (op U))).inv
        ⟨⟨(K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op U) x.1 x.2,
          (K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op U) y.1 y.2⟩,
          @Subsingleton.elim PUnit inferInstance _ _⟩)
    ∀ {V : C} (f : V ⟶ U) (hf : Presheaf.imageSieve K.oneMap t f)
      {W : C} (r : W ⟶ V),
    let q := descentCounitLocalPreimage J K t f hf
    ∀ (b : Fin 2) {T : C} (s : T ⟶ W),
    let e := if b = 0 then x else y
    let qr : (⟨q.1, CategoryTheory.Over.mk ((s ≫ r) ≫ q.2)⟩ :
        OverSite (K.simplicial.obj (op ⦋1⦌))) ⟶
          ⟨q.1, CategoryTheory.Over.mk (r ≫ q.2)⟩ :=
      Sigma.SigmaHom.mk (CategoryTheory.Over.homMk s (Category.assoc s r q.2).symm)
    let pr : (⟨e.1, CategoryTheory.Over.mk (((s ≫ r) ≫ f) ≫ e.2)⟩ :
        OverSite (K.simplicial.obj (op ⦋0⦌))) ⟶
          ⟨e.1, CategoryTheory.Over.mk ((r ≫ f) ≫ e.2)⟩ :=
      Sigma.SigmaHom.mk (CategoryTheory.Over.homMk s
        ((Category.assoc s (r ≫ f) e.2).symm.trans
          (congrArg (fun a ↦ a ≫ e.2) (Category.assoc s r f).symm)))
    (overMap (K.simplicial.δ b)).map qr ≫ (descentCounitEndpointIso J K x y f hf r b).hom =
      (descentCounitEndpointIso J K x y f hf (s ≫ r) b).hom ≫ pr := sorry

/-- Evaluated Cartesian transitions and their inverses commute with fixed-lift endpoint
transport and restriction, through the canonical sheafification comparison. -/
private theorem descentCounitEndpointIso_transition
    (G : Cartesian J K.simplicial A) {U : C}
    (x y : Σ i : (K.simplicial.obj (op ⦋0⦌)).I,
      U ⟶ (K.simplicial.obj (op ⦋0⦌)).obj i) :
    let t := (pullbackObjIso K.zeroMap K.zeroMap (op U)).inv
      ((Types.pullbackIsoPullback (K.zeroMap.app (op U)) (K.zeroMap.app (op U))).inv
        ⟨⟨(K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op U) x.1 x.2,
          (K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op U) y.1 y.2⟩,
          @Subsingleton.elim PUnit inferInstance _ _⟩)
    ∀ {V : C} (f : V ⟶ U) (hf : Presheaf.imageSieve K.oneMap t f)
      {W : C} (r : W ⟶ V),
    let q := descentCounitLocalPreimage J K t f hf
    ∀ (b : Fin 2) {T : C} (s : T ⟶ W),
    let e := if b = 0 then x else y
    let qr : (⟨q.1, CategoryTheory.Over.mk ((s ≫ r) ≫ q.2)⟩ :
        OverSite (K.simplicial.obj (op ⦋1⦌))) ⟶
          ⟨q.1, CategoryTheory.Over.mk (r ≫ q.2)⟩ :=
      Sigma.SigmaHom.mk (CategoryTheory.Over.homMk s (Category.assoc s r q.2).symm)
    let pr : (⟨e.1, CategoryTheory.Over.mk (((s ≫ r) ≫ f) ≫ e.2)⟩ :
        OverSite (K.simplicial.obj (op ⦋0⦌))) ⟶
          ⟨e.1, CategoryTheory.Over.mk ((r ≫ f) ≫ e.2)⟩ :=
      Sigma.SigmaHom.mk (CategoryTheory.Over.homMk s
        ((Category.assoc s (r ≫ f) e.2).symm.trans
          (congrArg (fun a ↦ a ≫ e.2) (Category.assoc s r f).symm)))
    let J₀ := (overSitePrecoverage J K.simplicial (op ⦋0⦌)).toGrothendieck
    let J₁ := (overSitePrecoverage J K.simplicial (op ⦋1⦌)).toGrothendieck
    let u := overMap (K.simplicial.δ b)
    let topEq := fun n : SimplexCategory ↦
      (Coverage.toGrothendieck_toPrecoverage (overTopology J
        (K.simplicial.obj (op n))).toCoverage).trans
        ((Coverage.gi _).l_u_eq (overTopology J (K.simplicial.obj (op n))))
    let hcont : u.IsContinuous J₁ J₀ :=
      Eq.mpr (congrArg₂ (fun T₁ T₀ ↦ u.IsContinuous T₁ T₀) (topEq ⦋1⦌) (topEq ⦋0⦌))
        (overMap_isContinuous J (K.simplicial.δ b))
    let G₀ := (Grothendieck.fiberRestrict (overSiteDiagram K.simplicial)
      (overSitePrecoverage J K.simplicial) A ⦋0⦌).obj G.obj
    let G₁ := (Grothendieck.fiberRestrict (overSiteDiagram K.simplicial)
      (overSitePrecoverage J K.simplicial) A ⦋1⦌).obj G.obj
    let c := isoSheafify J₁
      (@Functor.op_comp_isSheaf _ _ _ _ u A _ J₁ J₀ hcont G₀)
    let τ := @asIso _ _ _ _
      (Grothendieck.Sheaf.sheafTransition (overSiteDiagram K.simplicial)
        (overSitePrecoverage J K.simplicial) A (SimplexCategory.δ b) G.obj)
      (G.property.isIso_transition (SimplexCategory.δ b))
    let Q : OverSite (K.simplicial.obj (op ⦋1⦌)) :=
      ⟨q.1, CategoryTheory.Over.mk (r ≫ q.2)⟩
    let Q' : OverSite (K.simplicial.obj (op ⦋1⦌)) :=
      ⟨q.1, CategoryTheory.Over.mk ((s ≫ r) ≫ q.2)⟩
    let eV := descentCounitEndpointIso J K x y f hf r b
    let eW := descentCounitEndpointIso J K x y f hf (s ≫ r) b
    (G₁.obj.map qr.op ≫ τ.inv.hom.app (op Q') ≫ c.inv.app (op Q') ≫
        G₀.obj.map eW.inv.op =
      τ.inv.hom.app (op Q) ≫ c.inv.app (op Q) ≫ G₀.obj.map eV.inv.op ≫
        G₀.obj.map pr.op) ∧
      (G₀.obj.map pr.op ≫ G₀.obj.map eW.hom.op ≫ c.hom.app (op Q') ≫
          τ.hom.hom.app (op Q') =
        G₀.obj.map eV.hom.op ≫ c.hom.app (op Q) ≫ τ.hom.hom.app (op Q) ≫
          G₁.obj.map qr.op) := sorry

/-- Local degree-one lifts transfer a Cartesian section to a family over a target vertex. -/
private def descentCounitInvFamily (G : Cartesian J K.simplicial A)
    (X : Grothendieck (overSiteDiagram K.simplicial))
    (Y : StructuredArrow (op ((totalForget K.simplicial).obj X))
      (totalForget K.simplicial).op) :
    let X₀ := (overMap (K.simplicial.map
      (SimplexCategory.const ⦋0⦌ X.base.unop 0).op)).obj X.fiber
    let Y₀ := (overMap (K.simplicial.map
      (SimplexCategory.const ⦋0⦌ Y.right.unop.base.unop 0).op)).obj Y.right.unop.fiber
    let x : Σ i : (K.simplicial.obj (op ⦋0⦌)).I,
        Y₀.2.left ⟶ (K.simplicial.obj (op ⦋0⦌)).obj i :=
      ⟨X₀.1, Y.hom.unop ≫ X₀.2.hom⟩
    let y : Σ i : (K.simplicial.obj (op ⦋0⦌)).I,
        Y₀.2.left ⟶ (K.simplicial.obj (op ⦋0⦌)).obj i := ⟨Y₀.1, Y₀.2.hom⟩
    let t := (pullbackObjIso K.zeroMap K.zeroMap (op Y₀.2.left)).inv
      ((Types.pullbackIsoPullback (K.zeroMap.app (op Y₀.2.left))
        (K.zeroMap.app (op Y₀.2.left))).inv
          ⟨⟨(K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op Y₀.2.left) x.1 x.2,
            (K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op Y₀.2.left) y.1 y.2⟩,
              @Subsingleton.elim PUnit inferInstance _ _⟩)
    let S : (J.over ((K.simplicial.obj (op ⦋0⦌)).obj Y₀.1)).Cover Y₀.2 :=
      ⟨(Sieve.overEquiv Y₀.2).symm (Presheaf.imageSieve K.oneMap t),
        J.overEquiv_symm_mem_over Y₀.2 _ (K.one_locallySurjective.imageSieve_mem t)⟩
    let G₀ := (Grothendieck.fiberRestrict (overSiteDiagram K.simplicial)
      (overSitePrecoverage J K.simplicial) A ⦋0⦌).obj G.obj
    let P := (overIncl (K.simplicial.obj (op ⦋0⦌)) Y₀.1).op ⋙ G₀.obj
    ∀ I : S.Arrow, G.obj.obj.obj (op X) ⟶ P.obj (op I.Y) :=
    let X₀ := (overMap (K.simplicial.map
      (SimplexCategory.const ⦋0⦌ X.base.unop 0).op)).obj X.fiber
    let Y₀ := (overMap (K.simplicial.map
      (SimplexCategory.const ⦋0⦌ Y.right.unop.base.unop 0).op)).obj Y.right.unop.fiber
    let x : Σ i : (K.simplicial.obj (op ⦋0⦌)).I,
        Y₀.2.left ⟶ (K.simplicial.obj (op ⦋0⦌)).obj i :=
      ⟨X₀.1, Y.hom.unop ≫ X₀.2.hom⟩
    let y : Σ i : (K.simplicial.obj (op ⦋0⦌)).I,
        Y₀.2.left ⟶ (K.simplicial.obj (op ⦋0⦌)).obj i := ⟨Y₀.1, Y₀.2.hom⟩
    let t := (pullbackObjIso K.zeroMap K.zeroMap (op Y₀.2.left)).inv
      ((Types.pullbackIsoPullback (K.zeroMap.app (op Y₀.2.left))
        (K.zeroMap.app (op Y₀.2.left))).inv
          ⟨⟨(K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op Y₀.2.left) x.1 x.2,
            (K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op Y₀.2.left) y.1 y.2⟩,
              @Subsingleton.elim PUnit inferInstance _ _⟩)
    let S : (J.over ((K.simplicial.obj (op ⦋0⦌)).obj Y₀.1)).Cover Y₀.2 :=
      ⟨(Sieve.overEquiv Y₀.2).symm (Presheaf.imageSieve K.oneMap t),
        J.overEquiv_symm_mem_over Y₀.2 _ (K.one_locallySurjective.imageSieve_mem t)⟩
    let G₀ := (Grothendieck.fiberRestrict (overSiteDiagram K.simplicial)
      (overSitePrecoverage J K.simplicial) A ⦋0⦌).obj G.obj
    let P := (overIncl (K.simplicial.obj (op ⦋0⦌)) Y₀.1).op ⋙ G₀.obj
    fun I ↦
    let rawIso := fun {m n : SimplexCategory} (φ : m ⟶ n) ↦
      let Jm := (overSitePrecoverage J K.simplicial (op m)).toGrothendieck
      let Jn := (overSitePrecoverage J K.simplicial (op n)).toGrothendieck
      let u := overMap (K.simplicial.map φ.op)
      let topEq := fun k : SimplexCategory ↦
        (Coverage.toGrothendieck_toPrecoverage
          (overTopology J (K.simplicial.obj (op k))).toCoverage).trans
            ((Coverage.gi _).l_u_eq (overTopology J (K.simplicial.obj (op k))))
      let hcont : u.IsContinuous Jn Jm :=
        Eq.mpr (congrArg₂ (fun Tn Tm ↦ u.IsContinuous Tn Tm) (topEq n) (topEq m))
          (overMap_isContinuous J (K.simplicial.map φ.op))
      let Gm := (Grothendieck.fiberRestrict (overSiteDiagram K.simplicial)
        (overSitePrecoverage J K.simplicial) A m).obj G.obj
      let c := isoSheafify Jn
        (@Functor.op_comp_isSheaf _ _ _ _ u A _ Jn Jm hcont Gm)
      let τ := @asIso _ _ _ _
        (Grothendieck.Sheaf.sheafTransition (overSiteDiagram K.simplicial)
          (overSitePrecoverage J K.simplicial) A φ G.obj) (G.property.isIso_transition φ)
      c ≪≫ (sheafToPresheaf Jn A).mapIso τ
    let q := descentCounitLocalPreimage J K t I.f.left I.hf
    let Q : OverSite (K.simplicial.obj (op ⦋1⦌)) :=
      ⟨q.1, CategoryTheory.Over.mk (𝟙 I.Y.left ≫ q.2)⟩
    let e₀ := descentCounitEndpointIso J K x y I.f.left I.hf (𝟙 I.Y.left) 0
    let e₁ := descentCounitEndpointIso J K x y I.f.left I.hf (𝟙 I.Y.left) 1
    let a : (⟨x.1, CategoryTheory.Over.mk
        ((𝟙 I.Y.left ≫ I.f.left) ≫ x.2)⟩ :
          OverSite (K.simplicial.obj (op ⦋0⦌))) ⟶ X₀ :=
      Sigma.SigmaHom.mk (CategoryTheory.Over.homMk (I.f.left ≫ Y.hom.unop)
        ((Category.assoc I.f.left Y.hom.unop X₀.2.hom).trans
          (congrArg (fun b ↦ b ≫ x.2) (Category.id_comp I.f.left).symm)))
    let eY := (overIncl (K.simplicial.obj (op ⦋0⦌)) Y₀.1).mapIso
      (CategoryTheory.Over.isoMk (f := CategoryTheory.Over.mk
        ((𝟙 I.Y.left ≫ I.f.left) ≫ y.2)) (g := I.Y) (Iso.refl I.Y.left)
          ((Category.id_comp I.Y.hom).trans ((CategoryTheory.Over.w I.f).symm.trans
            (congrArg (fun b ↦ b ≫ y.2) (Category.id_comp I.f.left).symm))))
    (rawIso (SimplexCategory.const ⦋0⦌ X.base.unop 0)).inv.app (op X.fiber) ≫
      G₀.obj.map a.op ≫ G₀.obj.map e₀.hom.op ≫
      (rawIso (SimplexCategory.δ 0)).hom.app (op Q) ≫
      (rawIso (SimplexCategory.δ 1)).inv.app (op Q) ≫
      G₀.obj.map e₁.inv.op ≫ G₀.obj.map eY.inv.op

/-- Local Cartesian transfer maps agree on all overlaps of the matching-map cover. -/
private theorem descentCounitInvFamily_compatible (G : Cartesian J K.simplicial A)
    (X : Grothendieck (overSiteDiagram K.simplicial))
    (Y : StructuredArrow (op ((totalForget K.simplicial).obj X))
      (totalForget K.simplicial).op) :
    let X₀ := (overMap (K.simplicial.map
      (SimplexCategory.const ⦋0⦌ X.base.unop 0).op)).obj X.fiber
    let Y₀ := (overMap (K.simplicial.map
      (SimplexCategory.const ⦋0⦌ Y.right.unop.base.unop 0).op)).obj Y.right.unop.fiber
    let x : Σ i : (K.simplicial.obj (op ⦋0⦌)).I,
        Y₀.2.left ⟶ (K.simplicial.obj (op ⦋0⦌)).obj i :=
      ⟨X₀.1, Y.hom.unop ≫ X₀.2.hom⟩
    let y : Σ i : (K.simplicial.obj (op ⦋0⦌)).I,
        Y₀.2.left ⟶ (K.simplicial.obj (op ⦋0⦌)).obj i := ⟨Y₀.1, Y₀.2.hom⟩
    let t := (pullbackObjIso K.zeroMap K.zeroMap (op Y₀.2.left)).inv
      ((Types.pullbackIsoPullback (K.zeroMap.app (op Y₀.2.left))
        (K.zeroMap.app (op Y₀.2.left))).inv
          ⟨⟨(K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op Y₀.2.left) x.1 x.2,
            (K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op Y₀.2.left) y.1 y.2⟩,
              @Subsingleton.elim PUnit inferInstance _ _⟩)
    let S : (J.over ((K.simplicial.obj (op ⦋0⦌)).obj Y₀.1)).Cover Y₀.2 :=
      ⟨(Sieve.overEquiv Y₀.2).symm (Presheaf.imageSieve K.oneMap t),
        J.overEquiv_symm_mem_over Y₀.2 _ (K.one_locallySurjective.imageSieve_mem t)⟩
    let G₀ := (Grothendieck.fiberRestrict (overSiteDiagram K.simplicial)
      (overSitePrecoverage J K.simplicial) A ⦋0⦌).obj G.obj
    let P := (overIncl (K.simplicial.obj (op ⦋0⦌)) Y₀.1).op ⋙ G₀.obj
    ∀ ⦃I₁ I₂ : S.Arrow⦄ (r : I₁.Relation I₂),
      descentCounitInvFamily J K A G X Y I₁ ≫ P.map r.g₁.op =
        descentCounitInvFamily J K A G X Y I₂ ≫ P.map r.g₂.op := sorry

/-- Amalgamating local transfer maps supplies a cone over the right-Kan-extension diagram. -/
private def descentCounitCone (G : Cartesian J K.simplicial A)
    (X : Grothendieck (overSiteDiagram K.simplicial)) :
    Cone (StructuredArrow.proj (op ((totalForget K.simplicial).obj X))
      (totalForget K.simplicial).op ⋙ G.obj.obj) where
  pt := G.obj.obj.obj (op X)
  π :=
    { app := fun Y ↦
        let X₀ := (overMap (K.simplicial.map
          (SimplexCategory.const ⦋0⦌ X.base.unop 0).op)).obj X.fiber
        let Y₀ := (overMap (K.simplicial.map
          (SimplexCategory.const ⦋0⦌ Y.right.unop.base.unop 0).op)).obj Y.right.unop.fiber
        let x : Σ i : (K.simplicial.obj (op ⦋0⦌)).I,
            Y₀.2.left ⟶ (K.simplicial.obj (op ⦋0⦌)).obj i :=
          ⟨X₀.1, Y.hom.unop ≫ X₀.2.hom⟩
        let y : Σ i : (K.simplicial.obj (op ⦋0⦌)).I,
            Y₀.2.left ⟶ (K.simplicial.obj (op ⦋0⦌)).obj i := ⟨Y₀.1, Y₀.2.hom⟩
        let t := (pullbackObjIso K.zeroMap K.zeroMap (op Y₀.2.left)).inv
          ((Types.pullbackIsoPullback (K.zeroMap.app (op Y₀.2.left))
            (K.zeroMap.app (op Y₀.2.left))).inv
              ⟨⟨(K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op Y₀.2.left) x.1 x.2,
                (K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op Y₀.2.left) y.1 y.2⟩,
                  @Subsingleton.elim PUnit inferInstance _ _⟩)
        let S : (J.over ((K.simplicial.obj (op ⦋0⦌)).obj Y₀.1)).Cover Y₀.2 :=
          ⟨(Sieve.overEquiv Y₀.2).symm (Presheaf.imageSieve K.oneMap t),
            J.overEquiv_symm_mem_over Y₀.2 _ (K.one_locallySurjective.imageSieve_mem t)⟩
        let G₀ := (Grothendieck.fiberRestrict (overSiteDiagram K.simplicial)
          (overSitePrecoverage J K.simplicial) A ⦋0⦌).obj G.obj
        let P := (overIncl (K.simplicial.obj (op ⦋0⦌)) Y₀.1).op ⋙ G₀.obj
        let rawIso := fun {m n : SimplexCategory} (φ : m ⟶ n) ↦
          let Jm := (overSitePrecoverage J K.simplicial (op m)).toGrothendieck
          let Jn := (overSitePrecoverage J K.simplicial (op n)).toGrothendieck
          let u := overMap (K.simplicial.map φ.op)
          let topEq := fun k : SimplexCategory ↦
            (Coverage.toGrothendieck_toPrecoverage
              (overTopology J (K.simplicial.obj (op k))).toCoverage).trans
                ((Coverage.gi _).l_u_eq (overTopology J (K.simplicial.obj (op k))))
          let hcont : u.IsContinuous Jn Jm :=
            Eq.mpr (congrArg₂ (fun Tn Tm ↦ u.IsContinuous Tn Tm) (topEq n) (topEq m))
              (overMap_isContinuous J (K.simplicial.map φ.op))
          let Gm := (Grothendieck.fiberRestrict (overSiteDiagram K.simplicial)
            (overSitePrecoverage J K.simplicial) A m).obj G.obj
          let c := isoSheafify Jn
            (@Functor.op_comp_isSheaf _ _ _ _ u A _ Jn Jm hcont Gm)
          let τ := @asIso _ _ _ _
            (Grothendieck.Sheaf.sheafTransition (overSiteDiagram K.simplicial)
              (overSitePrecoverage J K.simplicial) A φ G.obj) (G.property.isIso_transition φ)
          c ≪≫ (sheafToPresheaf Jn A).mapIso τ
        let topEq := (Coverage.toGrothendieck_toPrecoverage
          (overTopology J (K.simplicial.obj (op ⦋0⦌))).toCoverage).trans
            ((Coverage.gi _).l_u_eq (overTopology J (K.simplicial.obj (op ⦋0⦌))))
        let hG₀ := Eq.mp (congrArg (fun T ↦ Presheaf.IsSheaf T G₀.obj) topEq) G₀.property
        let hP := @Functor.op_comp_isSheaf _ _ _ _
          (overIncl (K.simplicial.obj (op ⦋0⦌)) Y₀.1) A _
          (J.over ((K.simplicial.obj (op ⦋0⦌)).obj Y₀.1))
          (overTopology J (K.simplicial.obj (op ⦋0⦌)))
          (Sigma.incl_isContinuous (fun i ↦ J.over ((K.simplicial.obj (op ⦋0⦌)).obj i)) Y₀.1)
          ⟨G₀.obj, hG₀⟩
        hP.amalgamate S (descentCounitInvFamily J K A G X Y)
            (descentCounitInvFamily_compatible J K A G X Y) ≫
          (rawIso (SimplexCategory.const ⦋0⦌ Y.right.unop.base.unop 0)).hom.app
            (op Y.right.unop.fiber)
      naturality := sorry }

/-- The actual pointwise right-Kan-extension limit reconstructs the inverse-counit component. -/
private def descentCounitInvApp (G : Cartesian J K.simplicial A) :
    G.obj ⟶ (inverseImage J K.simplicial A).obj ((directImage J K.simplicial A).obj G.obj) :=
  ObjectProperty.homMk
    { app := fun X ↦
        ((totalForget K.simplicial).op.isPointwiseRightKanExtensionRanCounit G.obj.obj
          (op ((totalForget K.simplicial).obj X.unop))).lift
            (descentCounitCone J K A G X.unop)
      naturality := sorry }

/-- Cartesian reconstruction is a natural inverse to the augmentation counit. -/
@[no_expose] def descentCounitInv :
    (cartesianProperty J K.simplicial A).ι ⟶
      cartesianInverse J K A ⋙ inverseImage J K.simplicial A where
  app := descentCounitInvApp J K A
  naturality := sorry

/-- Cartesian reconstruction and the canonical counit satisfy both inverse identities. -/
theorem descentCounitInv_spec :
    whiskerLeft (cartesianProperty J K.simplicial A).ι
        (sheafLocalizationAdjunction J K A).counit ≫ descentCounitInv J K A = 𝟙 _ ∧
      descentCounitInv J K A ≫ whiskerLeft (cartesianProperty J K.simplicial A).ι
        (sheafLocalizationAdjunction J K A).counit = 𝟙 _ := sorry

/-- The preimage of a morphism under augmentation inverse image is the unit,
followed by direct image of that morphism and the explicit gluing inverse of the unit. -/
def inverseImage_preimage {X Y : Sheaf J A}
    (f : (inverseImage J K.simplicial A).obj X ⟶ (inverseImage J K.simplicial A).obj Y) :
    X ⟶ Y :=
  (sheafLocalizationAdjunction J K A).unit.app X ≫
    (directImage J K.simplicial A).map f ≫ (descentUnitInv J K A).app Y

/-- The explicit morphism preimage is inverse to the morphism action of augmentation pullback. -/
theorem inverseImage_preimage_spec :
    (∀ {X Y : Sheaf J A}
      (f : (inverseImage J K.simplicial A).obj X ⟶ (inverseImage J K.simplicial A).obj Y),
      (inverseImage J K.simplicial A).map (inverseImage_preimage J K A f) = f) ∧
      (∀ {X Y : Sheaf J A} (f : X ⟶ Y),
        inverseImage_preimage J K A ((inverseImage J K.simplicial A).map f) = f) := sorry

/-- Inverse image `a⁻¹` along a hypercovering is full. -/
instance inverseImage_full : (inverseImage J K.simplicial A).Full :=
  sorry

/-- Inverse image `a⁻¹` along a hypercovering is faithful. -/
instance inverseImage_faithful : (inverseImage J K.simplicial A).Faithful :=
  sorry

/-- Inverse image `a⁻¹` along a hypercovering is fully faithful. -/
def inverseImage_fullyFaithful : (inverseImage J K.simplicial A).FullyFaithful :=
  { preimage := inverseImage_preimage J K A
    map_preimage := (inverseImage_preimage_spec J K A).1
    preimage_map := (inverseImage_preimage_spec J K A).2 }

/-- The unit of `a⁻¹ ⊣ a_*` is an isomorphism. -/
theorem unit_app_isIso (F : Sheaf J A) :
    IsIso ((sheafLocalizationAdjunction J K A).unit.app F) :=
  sorry

/-- The counit of `a⁻¹ ⊣ a_*` is an isomorphism precisely on cartesian sheaves. -/
theorem counit_app_isIso_iff_isCartesian
    (G : Sheaf (overSiteTotalTopology J K.simplicial) A) :
    IsIso ((sheafLocalizationAdjunction J K A).counit.app G) ↔
      IsCartesian J K.simplicial A G :=
  sorry

/-- The counit of `a⁻¹ ⊣ a_*` is an isomorphism on a cartesian sheaf. -/
theorem counit_app_isIso_of_isCartesian
    (G : Sheaf (overSiteTotalTopology J K.simplicial) A)
    (h : IsCartesian J K.simplicial A G) :
    IsIso ((sheafLocalizationAdjunction J K A).counit.app G) :=
  sorry

/-- A sheaf on `(C / K)_total` lies in the essential image of `a⁻¹` if and only if it is
cartesian. -/
theorem mem_essImage_iff_isCartesian
    (G : Sheaf (overSiteTotalTopology J K.simplicial) A) :
    (inverseImage J K.simplicial A).essImage G ↔ IsCartesian J K.simplicial A G :=
  sorry

/-- The descent unit isomorphism has the actual adjunction unit as forward map and
its gluing reconstruction as inverse map. -/
def cartesianUnitIso :
    𝟭 (Sheaf J A) ≅ cartesianFunctor J K A ⋙ cartesianInverse J K A :=
  { hom := (sheafLocalizationAdjunction J K A).unit
    inv := descentUnitInv J K A
    hom_inv_id := (descentUnitInv_spec J K A).1
    inv_hom_id := (descentUnitInv_spec J K A).2 }

/-- The forward component of the descent unit isomorphism is the canonical adjunction unit. -/
theorem cartesianUnitIso_hom_app (F : Sheaf J A) :
    (cartesianUnitIso J K A).hom.app F = (sheafLocalizationAdjunction J K A).unit.app F :=
  sorry

/-- The descent counit isomorphism has the actual adjunction counit as forward map
and Cartesian reconstruction as inverse map. -/
def cartesianCounitIso :
    cartesianInverse J K A ⋙ cartesianFunctor J K A ≅ 𝟭 (Cartesian J K.simplicial A) :=
  NatIso.ofComponents
    (fun G ↦ (cartesianProperty J K.simplicial A).isoMk
      { hom := (sheafLocalizationAdjunction J K A).counit.app G.obj
        inv := (descentCounitInv J K A).app G
        hom_inv_id := NatTrans.congr_app (descentCounitInv_spec J K A).1 G
        inv_hom_id := NatTrans.congr_app (descentCounitInv_spec J K A).2 G })
    (fun {G H} f ↦ ObjectProperty.hom_ext (cartesianProperty J K.simplicial A)
      ((sheafLocalizationAdjunction J K A).counit.naturality f.hom))

/-- The forward component of the descent counit isomorphism is the canonical adjunction counit. -/
theorem cartesianCounitIso_hom_app_hom (G : Cartesian J K.simplicial A) :
    ((cartesianCounitIso J K A).hom.app G).hom =
      (sheafLocalizationAdjunction J K A).counit.app G.obj := sorry

/-- If `K` is a hypercovering of the terminal presheaf, then `a⁻¹` implements an equivalence
between sheaves on `C` and cartesian sheaves on `(C / K)_total`, with quasi-inverse `a_*`. -/
def cartesianEquivalence : Sheaf J A ≌ Cartesian J K.simplicial A :=
  Equivalence.mk (cartesianFunctor J K A) (cartesianInverse J K A)
    (cartesianUnitIso J K A) (cartesianCounitIso J K A)

/-- The forward functor of `cartesianEquivalence` is `a⁻¹` corestricted to cartesian sheaves. -/
theorem cartesianEquivalence_functor :
    (cartesianEquivalence J K A).functor = cartesianFunctor J K A :=
  sorry

/-- The inverse functor of `cartesianEquivalence` is `a_*` on cartesian sheaves. -/
theorem cartesianEquivalence_inverse :
    (cartesianEquivalence J K A).inverse = cartesianInverse J K A :=
  sorry

end CategoryTheory.SemiRepresentableFamily
