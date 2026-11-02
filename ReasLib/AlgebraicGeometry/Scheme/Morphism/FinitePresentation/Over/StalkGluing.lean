/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.Grothendieck
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import Mathlib.CategoryTheory.Localization.Construction
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation.Yoneda
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Over
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Cat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-presentation gluing over a stalk

This leaf packages the neighborhood index, punctured-stalk open, and categorical pullback used to
compare finite-presentation schemes near a point with gluing data over the open complement and the
local scheme.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry
open scoped AlgebraicGeometry
open scoped CategoryTheory.Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The opposite ordered index of open neighborhoods `W` of `s` containing a fixed open `U`. -/
abbrev OpenNeighborhoodIndex (S : Scheme.{u}) (U : S.Opens) (s : S) : Type u :=
  ({ W : S.Opens // U ≤ W ∧ s ∈ (W : Set S) })ᵒᵖ

namespace OpenNeighborhoodIndex

/-- The underlying open subset of an open-neighborhood index object. -/
abbrev toOpen {S : Scheme.{u}} {U : S.Opens} {s : S}
    (W : OpenNeighborhoodIndex S U s) : S.Opens :=
  W.unop.1

end OpenNeighborhoodIndex

/-- The open `Spec(𝒪_{S,s}) ×_S U`, i.e. the intersection of the canonical stalk scheme with
`U`. -/
abbrev stalkOpenIntersection (S : Scheme.{u}) (U : S.Opens) (s : S) :
    (Spec (S.presheaf.stalk s)).Opens :=
  (S.fromSpecStalk s) ⁻¹ᵁ U

/-- The category of finite-presentation gluing data over `U`, over the stalk scheme, and over their
intersection. -/
abbrev finitePresentationStalkGluingCategory
    (S : Scheme.{u}) (U : S.Opens) (s : S) : Type (u + 1) :=
  CategoricalPullback
    (FinitePresentationOver.baseChange ((S.fromSpecStalk s) ∣_ U))
    (FinitePresentationOver.baseChange ((stalkOpenIntersection S U s).ι))

namespace FinitePresentationOver.OpenNeighborhood

/-- The pseudofunctor of finite-presentation schemes over open neighborhoods of a point,
with transition functors given by base change along inclusions of neighborhoods. -/
noncomputable def pseudofunctor (S : Scheme.{u}) (U : S.Opens) (s : S) :
    LocallyDiscrete (OpenNeighborhoodIndex S U s) ⥤ᵖ Cat.{u} := by
  let Q : LocallyDiscrete Scheme.{u} ⥤ᵖ Bicategory.Adj Cat.{u} :=
    LocallyDiscrete.mkPseudofunctor
      (fun X ↦ Bicategory.Adj.mk (Cat.of (Over X)))
      (fun f ↦ Bicategory.Adj.Hom.mk (Over.mapPullbackAdj f).toCat)
      (fun X ↦ Bicategory.Adj.iso₂Mk
        (Cat.Hom.isoMk (Over.mapId X)) (Cat.Hom.isoMk Over.pullbackId.symm))
      (fun f g ↦ Bicategory.Adj.iso₂Mk
        (Cat.Hom.isoMk (Over.mapComp f g)) (Cat.Hom.isoMk (Over.pullbackComp f g).symm))
      (fun _ _ _ ↦ by
        apply Bicategory.Adj.hom₂_ext
        apply Cat.Hom₂.ext
        ext X
        apply Over.OverMorphism.ext
        rfl)
      (fun _ ↦ by
        apply Bicategory.Adj.hom₂_ext
        apply Cat.Hom₂.ext
        ext X
        apply Over.OverMorphism.ext
        rfl)
      (fun _ ↦ by
        apply Bicategory.Adj.hom₂_ext
        apply Cat.Hom₂.ext
        ext X
        apply Over.OverMorphism.ext
        rfl)
  let R : LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat.{u} :=
    LocallyDiscrete.mkPseudofunctor
      (fun X ↦ (Q.obj ⟨X.unop⟩).obj)
      (fun f ↦ (Q.map f.unop.toLoc).r)
      (fun X ↦ Bicategory.Adj.rIso (Q.mapId ⟨X.unop⟩))
      (fun f g ↦ Bicategory.Adj.rIso (Q.mapComp g.unop.toLoc f.unop.toLoc))
      (fun f g h ↦ by
        have H := (congrArg (fun k ↦ k.τr)
          (Q.map₂_associator h.unop.toLoc g.unop.toLoc f.unop.toLoc)).symm
        convert H using 1 <;> rfl)
      (fun f ↦ by
        have H := congrArg (fun k ↦ k.τr)
          (Q.map₂_right_unitor f.unop.toLoc)
        rw [← IsIso.inv_eq_inv]
        rw [IsIso.inv_comp, IsIso.inv_comp, Bicategory.inv_whiskerRight]
        simp only [unop_id, Quiver.Hom.id_toLoc, unop_comp,
          Quiver.Hom.comp_toLoc] at H ⊢
        rw [IsIso.inv_eq_of_hom_inv_id (λ_ (Q.map f.unop.toLoc).r).hom_inv_id]
        rw [IsIso.inv_eq_of_hom_inv_id
          (Bicategory.Adj.rIso (Q.mapId _)).hom_inv_id]
        rw [IsIso.inv_eq_of_hom_inv_id
          (Bicategory.Adj.rIso (Q.mapComp f.unop.toLoc (𝟙 _))).hom_inv_id]
        rw [inv_eqToHom]
        simp only [Bicategory.Adj.comp_τr, Bicategory.Adj.whiskerLeft_τr,
          Bicategory.Adj.rightUnitor_hom_τr] at H
        convert H.symm using 1 <;> rfl)
      (fun f ↦ by
        have H := congrArg (fun k ↦ k.τr)
          (Q.map₂_left_unitor f.unop.toLoc)
        rw [← IsIso.inv_eq_inv]
        rw [IsIso.inv_comp, IsIso.inv_comp, Bicategory.inv_whiskerLeft]
        simp only [unop_id, Quiver.Hom.id_toLoc, unop_comp,
          Quiver.Hom.comp_toLoc] at H ⊢
        rw [IsIso.inv_eq_of_hom_inv_id (ρ_ (Q.map f.unop.toLoc).r).hom_inv_id]
        rw [IsIso.inv_eq_of_hom_inv_id
          (Bicategory.Adj.rIso (Q.mapId _)).hom_inv_id]
        rw [IsIso.inv_eq_of_hom_inv_id
          (Bicategory.Adj.rIso (Q.mapComp (𝟙 _) f.unop.toLoc)).hom_inv_id]
        rw [inv_eqToHom]
        simp only [Bicategory.Adj.comp_τr, Bicategory.Adj.whiskerRight_τr,
          Bicategory.Adj.leftUnitor_hom_τr] at H
        convert H.symm using 1 <;> rfl)
  let G : OpenNeighborhoodIndex S U s ⥤ Scheme.{u}ᵒᵖ :=
    { obj := fun W ↦ Opposite.op W.toOpen.toScheme
      map := fun f ↦ (S.homOfLE (leOfHom f.unop)).op
      map_id := fun W ↦ Quiver.Hom.unop_inj (by
        simpa using S.homOfLE_rfl W.toOpen)
      map_comp := fun f g ↦ Quiver.Hom.unop_inj (by
        simpa using (S.homOfLE_homOfLE (leOfHom g.unop) (leOfHom f.unop)).symm) }
  let F := G.toPseudofunctor.comp R
  let P : F.ObjectProperty :=
    { prop := fun W ↦ finitePresentationOverProperty W.as.toOpen.toScheme }
  -- Local instance justification (proof-local temporary data): P.fullsubcategory requires this proof-valued preservation argument through typeclass search and selects no mathematical data.
  letI : P.IsClosedUnderMapObj :=
    { map_obj := fun hX f ↦ FinitePresentationOver.baseChange_mem
        (S.homOfLE (leOfHom f.as.unop)) ⟨_, hX⟩ }
  exact P.fullsubcategory

/-- The morphisms in the Grothendieck construction whose component in the target fiber is an
isomorphism. -/
def transitionMorphism (S : Scheme.{u}) (U : S.Opens) (s : S) :
    MorphismProperty (Pseudofunctor.Grothendieck (pseudofunctor S U s)) :=
  fun _ _ f ↦ IsIso f.fiber

/-- The categorical colimit of finite-presentation schemes over open neighborhoods, modeled by
localizing the Grothendieck construction at the fiberwise-isomorphism transition morphisms. -/
abbrev Colimit (S : Scheme.{u}) (U : S.Opens) (s : S) : Type (u + 1) :=
  (transitionMorphism S U s).Localization

end FinitePresentationOver.OpenNeighborhood

namespace FinitePresentationOver

/-- Base change of finite-presentation schemes along a composite is base change in two
steps, induced from mathlib's `Over.pullbackComp`. -/
noncomputable def baseChangeCompIso {T T' T'' : Scheme.{u}} (g : T' ⟶ T) (h : T'' ⟶ T') :
    baseChange g ⋙ baseChange h ≅ baseChange (h ≫ g) :=
  ((finitePresentationOverProperty T'').fullyFaithfulι.whiskeringRight
    (FinitePresentationOver T)).preimageIso
    (Functor.isoWhiskerLeft (inclusion T) (Over.pullbackComp h g).symm)

/-- The components of `baseChangeCompIso` are those of `Over.pullbackComp`. -/
theorem baseChangeCompIso_hom_app_hom {T T' T'' : Scheme.{u}} (g : T' ⟶ T) (h : T'' ⟶ T')
    (X : FinitePresentationOver T) :
    ((baseChangeCompIso g h).hom.app X).hom = (Over.pullbackComp h g).inv.app X.obj :=
  rfl

private theorem pullbackId_app_left {T : Scheme.{u}} (X : Over T) :
    (Over.pullbackId.hom.app X).left = pullback.fst X.hom (𝟙 T) := by
  have H := congrArg Over.Hom.left (conjugateEquiv_counit
    (Over.mapPullbackAdj (𝟙 T)) Adjunction.id (Over.mapId T).inv X)
  change (Over.pullbackId.hom.app X).left ≫ 𝟙 _ =
    𝟙 _ ≫ pullback.fst X.hom (𝟙 T) at H
  simpa only [Category.comp_id, Category.id_comp] using H

private theorem pullback_eqToHom_left_fst {T T' : Scheme.{u}} {f g : T' ⟶ T}
    (h : f = g) (X : Over T) :
    (eqToHom (congrArg (fun k ↦ (Over.pullback k).obj X) h)).left ≫
      pullback.fst X.hom g = pullback.fst X.hom f := by
  cases h
  simp

private theorem baseChangeCompIso_inv_app_fst_fst {T T' T'' : Scheme.{u}}
    (g : T' ⟶ T) (h : T'' ⟶ T') (X : FinitePresentationOver T) :
    ((baseChangeCompIso g h).inv.app X).hom.left ≫
        pullback.fst (pullback.snd X.obj.hom g) h ≫ pullback.fst X.obj.hom g =
      pullback.fst X.obj.hom (h ≫ g) := by
  have H := congrArg Over.Hom.left (conjugateEquiv_counit
    (Over.mapPullbackAdj (h ≫ g))
    ((Over.mapPullbackAdj h).comp (Over.mapPullbackAdj g))
    (Over.mapComp h g).inv X.obj)
  change ((baseChangeCompIso g h).inv.app X).hom.left ≫
      (pullback.fst (pullback.snd X.obj.hom g) h ≫ pullback.fst X.obj.hom g) =
    𝟙 _ ≫ pullback.fst X.obj.hom (h ≫ g) at H
  simpa only [Category.id_comp] using H

private theorem baseChangeComparison_inv_app_fst_fst {T T' T'' : Scheme.{u}}
    (g : T' ⟶ T) (h : T'' ⟶ T') (k : T'' ⟶ T) (hk : h ≫ g = k)
    (X : FinitePresentationOver T) :
    (((baseChangeCompIso g h ≪≫ eqToIso (congrArg baseChange hk)).app X).inv).hom.left ≫
        pullback.fst (pullback.snd X.obj.hom g) h ≫ pullback.fst X.obj.hom g =
      pullback.fst X.obj.hom k := by
  cases hk
  change (𝟙 _ ≫ ((baseChangeCompIso g h).inv.app X).hom).left ≫
      pullback.fst (pullback.snd X.obj.hom g) h ≫ pullback.fst X.obj.hom g = _
  simpa only [Category.id_comp] using baseChangeCompIso_inv_app_fst_fst g h X

private theorem baseChange_map_left_fst {T T' : Scheme.{u}} (g : T' ⟶ T)
    {X Y : FinitePresentationOver T} (f : X ⟶ Y) :
    ((baseChange g).map f).hom.left ≫ pullback.fst Y.obj.hom g =
      pullback.fst X.obj.hom g ≫ f.hom.left :=
  pullback.lift_fst _ _ _

end FinitePresentationOver

/-- The canonical identification of the two restrictions of a finite-presentation scheme
to `Spec(𝒪_{S,s}) ×_S U`: via `U` and via the stalk scheme. -/
noncomputable def finitePresentationStalkGluingIso (S : Scheme.{u}) (U : S.Opens) (s : S) :
    FinitePresentationOver.baseChange U.ι ⋙
        FinitePresentationOver.baseChange ((S.fromSpecStalk s) ∣_ U) ≅
      FinitePresentationOver.baseChange (S.fromSpecStalk s) ⋙
        FinitePresentationOver.baseChange (stalkOpenIntersection S U s).ι :=
  FinitePresentationOver.baseChangeCompIso _ _ ≪≫
    eqToIso (congrArg FinitePresentationOver.baseChange (morphismRestrict_ι _ _)) ≪≫
    (FinitePresentationOver.baseChangeCompIso _ _).symm

/-- The restriction functor of Stacks 0BPA: a finite-presentation scheme `X → S` goes to its
restrictions over `U` and over `Spec(𝒪_{S,s})`, glued by the canonical identification over
their intersection. -/
noncomputable def finitePresentationStalkGluingFunctor (S : Scheme.{u}) (U : S.Opens) (s : S) :
    FinitePresentationOver S ⥤ finitePresentationStalkGluingCategory S U s :=
  (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback _ _ _).obj
    { fst := FinitePresentationOver.baseChange U.ι
      snd := FinitePresentationOver.baseChange (S.fromSpecStalk s)
      iso := finitePresentationStalkGluingIso S U s }

/-- The `U`-component of the stalk-gluing restriction functor is base change to `U`. -/
@[simp]
theorem finitePresentationStalkGluingFunctor_obj_fst (S : Scheme.{u}) (U : S.Opens) (s : S)
    (X : FinitePresentationOver S) :
    ((finitePresentationStalkGluingFunctor S U s).obj X).fst =
      (FinitePresentationOver.baseChange U.ι).obj X :=
  rfl

/-- The local component of the stalk-gluing restriction functor is base change to
`Spec(𝒪_{S,s})`. -/
@[simp]
theorem finitePresentationStalkGluingFunctor_obj_snd (S : Scheme.{u}) (U : S.Opens) (s : S)
    (X : FinitePresentationOver S) :
    ((finitePresentationStalkGluingFunctor S U s).obj X).snd =
      (FinitePresentationOver.baseChange (S.fromSpecStalk s)).obj X :=
  rfl

/-- The gluing identification of the restriction functor is the canonical one. -/
@[simp]
theorem finitePresentationStalkGluingFunctor_obj_iso (S : Scheme.{u}) (U : S.Opens) (s : S)
    (X : FinitePresentationOver S) :
    ((finitePresentationStalkGluingFunctor S U s).obj X).iso =
      (finitePresentationStalkGluingIso S U s).app X :=
  rfl

namespace FinitePresentationOver.OpenNeighborhood

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem id_fiber_left (S : Scheme.{u}) (U : S.Opens) (s : S)
    (X : Pseudofunctor.Grothendieck (pseudofunctor S U s)) :
    (𝟙 X : X ⟶ X).fiber.hom.left =
      pullback.fst X.fiber.obj.hom (S.homOfLE (leOfHom (𝟙 X.base).unop)) := by
  change (((pseudofunctor S U s).mapId ⟨X.base⟩).hom.toNatTrans.app X.fiber).hom.left = _
  unfold pseudofunctor
  extract_lets Q R G F P
  change ((F.mapId ⟨X.base⟩).hom.toNatTrans.app X.fiber.obj).left = _
  change ((R.map₂ (G.toPseudofunctor.mapId ⟨X.base⟩).hom).toNatTrans.app X.fiber.obj ≫
    (R.mapId (G.toPseudofunctor.obj ⟨X.base⟩)).hom.toNatTrans.app X.fiber.obj).left = _
  simp only [Functor.toPseudofunctor_mapId, eqToIso,
    PrelaxFunctor.map₂_eqToHom, Cat.eqToHom_app]
  change (eqToHom (congrArg (fun f ↦ (Over.pullback f).obj X.fiber.obj)
    (S.homOfLE_rfl X.base.toOpen))).left ≫ (Over.pullbackId.hom.app X.fiber.obj).left = _
  rw [pullbackId_app_left]
  exact pullback_eqToHom_left_fst (S.homOfLE_rfl X.base.toOpen) X.fiber.obj

/-- Pull back neighborhood schemes along a compatible family of maps from a fixed scheme. -/
noncomputable def restrictionFunctor
    (S : Scheme.{u}) (U : S.Opens) (s : S) (T : Scheme.{u})
    (ι : (W : OpenNeighborhoodIndex S U s) → (T ⟶ W.toOpen.toScheme))
    (hι : ∀ {W W'} (f : W ⟶ W'), ι W' ≫ S.homOfLE (leOfHom f.unop) = ι W) :
    Pseudofunctor.Grothendieck (pseudofunctor S U s) ⥤ FinitePresentationOver T where
  obj X := (baseChange (ι X.base)).obj X.fiber
  map {X Y} f :=
    ((baseChangeCompIso (S.homOfLE (leOfHom f.base.unop)) (ι Y.base) ≪≫
      eqToIso (congrArg baseChange (hι f.base))).app X.fiber).inv ≫
        (baseChange (ι Y.base)).map f.fiber
  map_id := by
    intro X
    let φ : (baseChange (ι X.base)).obj X.fiber ⟶
        (baseChange (ι X.base)).obj X.fiber :=
      ((baseChangeCompIso (S.homOfLE (leOfHom (𝟙 X.base).unop)) (ι X.base) ≪≫
        eqToIso (congrArg baseChange (hι (𝟙 X.base)))).app X.fiber).inv ≫
          (baseChange (ι X.base)).map (𝟙 X : X ⟶ X).fiber
    change φ = 𝟙 _
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change
        ((((baseChangeCompIso (S.homOfLE (leOfHom (𝟙 X.base).unop)) (ι X.base) ≪≫
          eqToIso (congrArg baseChange (hι (𝟙 X.base)))).app X.fiber).inv).hom.left ≫
            ((baseChange (ι X.base)).map (𝟙 X : X ⟶ X).fiber).hom.left) ≫
              pullback.fst X.fiber.obj.hom (ι X.base) = 𝟙 _ ≫ _
      let e := ((baseChangeCompIso (S.homOfLE (leOfHom (𝟙 X.base).unop)) (ι X.base) ≪≫
        eqToIso (congrArg baseChange (hι (𝟙 X.base)))).app X.fiber).inv
      calc
        (e.hom.left ≫ ((baseChange (ι X.base)).map (𝟙 X : X ⟶ X).fiber).hom.left) ≫
            pullback.fst X.fiber.obj.hom (ι X.base) =
          e.hom.left ≫
            (pullback.fst ((baseChange (S.homOfLE (leOfHom (𝟙 X.base).unop))).obj
              X.fiber).obj.hom (ι X.base) ≫ (𝟙 X : X ⟶ X).fiber.hom.left) :=
          (Category.assoc _ _ _).trans (congrArg (fun k ↦ e.hom.left ≫ k)
            (baseChange_map_left_fst (ι X.base) (𝟙 X : X ⟶ X).fiber))
        _ = e.hom.left ≫
            (pullback.fst ((baseChange (S.homOfLE (leOfHom (𝟙 X.base).unop))).obj
              X.fiber).obj.hom (ι X.base) ≫
                pullback.fst X.fiber.obj.hom (S.homOfLE (leOfHom (𝟙 X.base).unop))) :=
          congrArg (fun k ↦ e.hom.left ≫
            (pullback.fst ((baseChange (S.homOfLE (leOfHom (𝟙 X.base).unop))).obj
              X.fiber).obj.hom (ι X.base) ≫ k)) (id_fiber_left S U s X)
        _ = pullback.fst X.fiber.obj.hom (ι X.base) :=
          baseChangeComparison_inv_app_fst_fst _ _ _ (hι (𝟙 X.base)) X.fiber
        _ = 𝟙 _ ≫ pullback.fst X.fiber.obj.hom (ι X.base) := (Category.id_comp _).symm
    · exact (Over.w φ.hom).trans (Category.id_comp _).symm
  map_comp := sorry

/-- Pullback along a compatible family sends an invertible fiber map to an isomorphism. -/
theorem restrictionFunctor_isIso
    (S : Scheme.{u}) (U : S.Opens) (s : S) (T : Scheme.{u})
    (ι : (W : OpenNeighborhoodIndex S U s) → (T ⟶ W.toOpen.toScheme))
    (hι : ∀ {W W'} (f : W ⟶ W'), ι W' ≫ S.homOfLE (leOfHom f.unop) = ι W)
    {X Y : Pseudofunctor.Grothendieck (pseudofunctor S U s)} (f : X ⟶ Y)
    (hf : IsIso f.fiber) :
    IsIso ((restrictionFunctor S U s T ι hι).map f) := by
  let φ : (baseChange (S.homOfLE (leOfHom f.base.unop))).obj X.fiber ⟶ Y.fiber :=
    f.fiber
  have hφ : IsIso φ := hf
  exact (((baseChangeCompIso (S.homOfLE (leOfHom f.base.unop)) (ι Y.base) ≪≫
    eqToIso (congrArg baseChange (hι f.base))).app X.fiber).symm ≪≫
      (baseChange (ι Y.base)).mapIso (@asIso _ _ _ _ φ hφ)).isIso_hom

/-- Restriction of neighborhood schemes to the fixed open subscheme. -/
noncomputable def openRestrictionFunctor (S : Scheme.{u}) (U : S.Opens) (s : S) :
    Pseudofunctor.Grothendieck (pseudofunctor S U s) ⥤
      FinitePresentationOver U.toScheme :=
  restrictionFunctor S U s U.toScheme
    (fun W ↦ S.homOfLE W.unop.property.1)
    (fun {_ W'} f ↦ S.homOfLE_homOfLE W'.unop.property.1 (leOfHom f.unop))

/-- The canonical maps from the stalk scheme to open neighborhoods commute with inclusions. -/
theorem stalkRestriction_compatibility
    (S : Scheme.{u}) (U : S.Opens) (s : S)
    {W W' : OpenNeighborhoodIndex S U s} (f : W ⟶ W') :
    W'.toOpen.fromSpecStalkOfMem s W'.unop.property.2 ≫
        S.homOfLE (leOfHom f.unop) =
      W.toOpen.fromSpecStalkOfMem s W.unop.property.2 := by
  apply (cancel_mono W.toOpen.ι).1
  simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Opens.fromSpecStalkOfMem_ι]

/-- Restriction of neighborhood schemes to the local scheme at the point. -/
noncomputable def stalkRestrictionFunctor (S : Scheme.{u}) (U : S.Opens) (s : S) :
    Pseudofunctor.Grothendieck (pseudofunctor S U s) ⥤
      FinitePresentationOver (Spec (S.presheaf.stalk s)) :=
  restrictionFunctor S U s _
    (fun W ↦ W.toOpen.fromSpecStalkOfMem s W.unop.property.2)
    (stalkRestriction_compatibility S U s)

/-- The maps from the stalk-open intersection to any neighborhood agree over that neighborhood. -/
theorem intersection_commutes
    (S : Scheme.{u}) (U : S.Opens) (s : S) (W : OpenNeighborhoodIndex S U s) :
    ((S.fromSpecStalk s) ∣_ U) ≫ S.homOfLE W.unop.property.1 =
      (stalkOpenIntersection S U s).ι ≫
        W.toOpen.fromSpecStalkOfMem s W.unop.property.2 := by
  apply (cancel_mono W.toOpen.ι).1
  simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Opens.fromSpecStalkOfMem_ι,
    morphismRestrict_ι]

/-- The two restrictions of a neighborhood scheme to the stalk-open intersection agree via
the canonical composition isomorphisms for base change. -/
noncomputable def restrictionGluingIso (S : Scheme.{u}) (U : S.Opens) (s : S) :
    openRestrictionFunctor S U s ⋙ baseChange ((S.fromSpecStalk s) ∣_ U) ≅
      stalkRestrictionFunctor S U s ⋙ baseChange (stalkOpenIntersection S U s).ι :=
  NatIso.ofComponents
    (fun X ↦ (baseChangeCompIso _ _).app X.fiber ≪≫
      eqToIso (congrArg (fun f ↦ (baseChange f).obj X.fiber)
        (intersection_commutes S U s X.base)) ≪≫
      ((baseChangeCompIso _ _).app X.fiber).symm)
    (by sorry)

/-- Restrict a scheme over an open neighborhood to the fixed open and to the stalk scheme. -/
noncomputable def grothendieckStalkGluingFunctor
    (S : Scheme.{u}) (U : S.Opens) (s : S) :
    Pseudofunctor.Grothendieck (pseudofunctor S U s) ⥤
      finitePresentationStalkGluingCategory S U s :=
  (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback _ _ _).obj
    { fst := openRestrictionFunctor S U s
      snd := stalkRestrictionFunctor S U s
      iso := restrictionGluingIso S U s }

/-- A transition with invertible fiber component restricts to isomorphisms on both pieces. -/
theorem grothendieckStalkGluingFunctor_inverts
    (S : Scheme.{u}) (U : S.Opens) (s : S) :
    (transitionMorphism S U s).IsInvertedBy (grothendieckStalkGluingFunctor S U s) := by
  intro X Y f hf
  apply (CategoricalPullback.isIso_iff
    (baseChange ((S.fromSpecStalk s) ∣_ U))
    (baseChange (stalkOpenIntersection S U s).ι)
    ((grothendieckStalkGluingFunctor S U s).map f)).mpr
  constructor
  · exact restrictionFunctor_isIso S U s U.toScheme
      (fun W ↦ S.homOfLE W.unop.property.1)
      (fun {_ W'} f ↦ S.homOfLE_homOfLE W'.unop.property.1 (leOfHom f.unop)) f hf
  · exact restrictionFunctor_isIso S U s (Spec (S.presheaf.stalk s))
      (fun W ↦ W.toOpen.fromSpecStalkOfMem s W.unop.property.2)
      (stalkRestriction_compatibility S U s) f hf

/-- The comparison from the neighborhood colimit to stalk-gluing data, induced by restriction
and the explicit localization construction. -/
noncomputable def stalkGluingFunctor (S : Scheme.{u}) (U : S.Opens) (s : S) :
    Colimit S U s ⥤ finitePresentationStalkGluingCategory S U s :=
  Localization.Construction.lift (grothendieckStalkGluingFunctor S U s)
    (grothendieckStalkGluingFunctor_inverts S U s)

/-- On the Grothendieck construction, the localized comparison is the restriction functor. -/
@[simp]
theorem stalkGluingFunctor_fac (S : Scheme.{u}) (U : S.Opens) (s : S) :
    (transitionMorphism S U s).Q ⋙ stalkGluingFunctor S U s =
      grothendieckStalkGluingFunctor S U s :=
  Localization.Construction.fac _ _

/-- The open component of the localized comparison is the base change of the neighborhood
scheme to the fixed open. -/
@[simp]
theorem stalkGluingFunctor_obj_fst (S : Scheme.{u}) (U : S.Opens) (s : S)
    (X : Pseudofunctor.Grothendieck (pseudofunctor S U s)) :
    ((stalkGluingFunctor S U s).obj ((transitionMorphism S U s).Q.obj X)).fst =
      (baseChange (S.homOfLE X.base.unop.property.1)).obj X.fiber := rfl

/-- The local component of the localized comparison is the base change of the neighborhood
scheme to the stalk scheme. -/
@[simp]
theorem stalkGluingFunctor_obj_snd (S : Scheme.{u}) (U : S.Opens) (s : S)
    (X : Pseudofunctor.Grothendieck (pseudofunctor S U s)) :
    ((stalkGluingFunctor S U s).obj ((transitionMorphism S U s).Q.obj X)).snd =
      (baseChange (X.base.toOpen.fromSpecStalkOfMem s X.base.unop.property.2)).obj
        X.fiber := rfl

/-- For a retrocompact open and a point outside it, restriction identifies the neighborhood
colimit with the category of stalk-gluing data. -/
@[stacks 0BQ5]
theorem stalkGluingFunctor_isEquivalence
    (S : Scheme.{u}) (U : S.Opens) [QuasiCompact U.ι]
    (s : S) (hsU : s ∉ (U : Set S)) :
    (stalkGluingFunctor S U s).IsEquivalence := sorry

end FinitePresentationOver.OpenNeighborhood

/-- Stacks 0BPA: for a closed point `s` with quasi-compact complement `U`, the restriction
functor from finite-presentation schemes over `S` to stalk-gluing data is an equivalence. -/
@[stacks 0BPA]
theorem finitePresentationStalkGluingFunctor_isEquivalence
    (S : Scheme.{u}) (U : S.Opens) [QuasiCompact U.ι]
    (s : S) (hs : s ∈ closedPoints S)
    (hU : (U : Set S) = ({s} : Set S)ᶜ) :
    (finitePresentationStalkGluingFunctor S U s).IsEquivalence := sorry

/-- Pulling the complement of a closed point back to its local scheme gives the punctured spectrum
of the local ring. -/
theorem stalkOpenIntersection_eq_puncturedOpen
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hx : x ∈ closedPoints X)
    (hU : (U : Set X) = ({x} : Set X)ᶜ) :
    stalkOpenIntersection X U x =
      PuncturedSpectrum.puncturedOpen (X.presheaf.stalk x) := by
  ext p
  change (X.fromSpecStalk x) p ∈ (U : Set X) ↔
    p ∉ ({IsLocalRing.closedPoint (X.presheaf.stalk x)} : Set _)
  rw [hU]
  change (X.fromSpecStalk x) p ≠ x ↔ p ≠ IsLocalRing.closedPoint (X.presheaf.stalk x)
  constructor
  · intro hp heq
    apply hp
    simpa only [heq] using (Scheme.fromSpecStalk_closedPoint (X := X) (x := x))
  · intro hp heq
    apply hp
    apply (X.fromSpecStalk x).isEmbedding.injective
    exact heq.trans (Scheme.fromSpecStalk_closedPoint (X := X) (x := x)).symm

/-- For a locally finitely presented target over a base scheme, a morphism from a scheme is
determined uniquely by its restrictions to the complement of a closed point and to the local
scheme at that point, provided the two restrictions agree on the canonical stalk-open
intersection. -/
theorem morphismsOverRestrictPuncturedLocalSpecBijective
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S)
    [LocallyOfFinitePresentation pY]
    (x : X) (hx : x ∈ closedPoints X)
    (U : X.Opens) (hU : (U : Set X) = ({x} : Set X)ᶜ)
    [QuasiCompact U.ι] :
    Set.BijOn
      (fun g : {g : X ⟶ Y // g ≫ pY = pX} ↦
        (U.ι ≫ g.1, X.fromSpecStalk x ≫ g.1))
      Set.univ
      ({ab : (U.toScheme ⟶ Y) × ((Spec (CommRingCat.of (X.presheaf.stalk x))) ⟶ Y) |
          ab.1 ≫ pY = U.ι ≫ pX} ∩
        {ab | ab.2 ≫ pY = X.fromSpecStalk x ≫ pX} ∩
        {ab | (X.fromSpecStalk x ∣_ U) ≫ ab.1 =
          (stalkOpenIntersection X U x).ι ≫ ab.2}) := sorry

end AlgebraicGeometry
