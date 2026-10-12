/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty
public import Mathlib.CategoryTheory.Bicategory.Grothendieck
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Cat
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally finite-presentation descent along directed affine limits

This leaf owns the quasi-compact, quasi-separated, locally finite-presentation
over-category and its object, morphism, and equality descent API for directed
inverse limits with affine transition maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open AlgebraicGeometry
open scoped CategoryTheory.Bicategory Pseudofunctor.StrongTrans

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Over.Qcqs

/-- The object property on `Over T` selecting quasi-compact, quasi-separated schemes locally of
finite presentation over `T`. -/
@[stacks 0EY1]
abbrev locallyFinitePresentationProperty (T : Scheme.{u}) :
    ObjectProperty (Over T) :=
  fun W ↦ CompactSpace W.left.carrier ∧
    QuasiSeparatedSpace W.left.carrier ∧ LocallyOfFinitePresentation W.hom

/-- The full subcategory of schemes over `T` whose source is quasi-compact and quasi-separated
and whose structure morphism to `T` is locally of finite presentation. -/
@[stacks 0EY1]
abbrev LocallyFinitePresentation (T : Scheme.{u}) : Type (u + 1) :=
  (locallyFinitePresentationProperty T).FullSubcategory

namespace LocallyFinitePresentation

/-- The inclusion of `LocallyFinitePresentation T` into all schemes over `T`. -/
abbrev inclusion (T : Scheme.{u}) :
    LocallyFinitePresentation T ⥤ Over T :=
  (locallyFinitePresentationProperty T).ι

/-- Objects of `LocallyFinitePresentation T` have quasi-compact source. -/
instance instCompactSpaceLeft (T : Scheme.{u}) (W : LocallyFinitePresentation T) :
    CompactSpace (W.obj.left : Scheme.{u}).carrier :=
  W.property.1

/-- Objects of `LocallyFinitePresentation T` have quasi-separated source. -/
instance instQuasiSeparatedSpaceLeft (T : Scheme.{u})
    (W : LocallyFinitePresentation T) :
    QuasiSeparatedSpace (W.obj.left : Scheme.{u}).carrier :=
  W.property.2.1

/-- Objects of `LocallyFinitePresentation T` are locally of finite presentation over
the base. -/
instance instLocallyOfFinitePresentationHom (T : Scheme.{u})
    (W : LocallyFinitePresentation T) :
    LocallyOfFinitePresentation W.obj.hom :=
  W.property.2.2

/-- Membership in `LocallyFinitePresentation T` exposes exactly the three source
conditions: quasi-compact source, quasi-separated source, and local finite presentation over
`T`. -/
theorem property_iff (T : Scheme.{u}) (W : Over T) :
    locallyFinitePresentationProperty T W ↔
      CompactSpace W.left.carrier ∧
        QuasiSeparatedSpace W.left.carrier ∧ LocallyOfFinitePresentation W.hom := Iff.rfl

/-- Base change sends objects of `LocallyFinitePresentation T` to objects of
`LocallyFinitePresentation T'`. -/
@[stacks 0EY1]
theorem baseChange_mem {T T' : Scheme.{u}} (f : T' ⟶ T) [IsAffineHom f]
    (W : Over T) (hW : locallyFinitePresentationProperty T W) :
    locallyFinitePresentationProperty T' ((Over.pullback f).obj W) := by
  -- Local instance justification (proof-local temporary data): unpack the supplied
  -- quasi-compactness hypothesis only for this base-change proof.
  haveI : CompactSpace W.left.carrier := hW.1
  -- Local instance justification (proof-local temporary data): unpack the supplied
  -- quasi-separatedness hypothesis only for this base-change proof.
  haveI : QuasiSeparatedSpace W.left.carrier := hW.2.1
  -- Local instance justification (proof-local temporary data): unpack the supplied local
  -- finite-presentation hypothesis only for this base-change proof.
  haveI : LocallyOfFinitePresentation W.hom := hW.2.2
  change CompactSpace (pullback W.hom f).carrier ∧
    QuasiSeparatedSpace (pullback W.hom f).carrier ∧
      LocallyOfFinitePresentation (pullback.snd W.hom f)
  exact ⟨inferInstance, quasiSeparatedSpace_of_quasiSeparated (pullback.fst W.hom f),
    inferInstance⟩

/-- Pullback along an affine morphism acts on quasi-compact, quasi-separated schemes that are
locally of finite presentation over the base. -/
noncomputable abbrev baseChange {T T' : Scheme.{u}} (f : T' ⟶ T) [IsAffineHom f] :
    LocallyFinitePresentation T ⥤ LocallyFinitePresentation T' :=
  (locallyFinitePresentationProperty T').lift
    (inclusion T ⋙ Over.pullback f) (fun W ↦ baseChange_mem f W.obj W.property)

namespace Descent

/-- The adjunction-valued pseudofunctor pairing extension and pullback between scheme slices. -/
private noncomputable def overAdjPseudofunctor :
    LocallyDiscrete Scheme.{u} ⥤ᵖ Bicategory.Adj Cat.{u} :=
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
      ext
      apply Over.OverMorphism.ext
      rfl)
    (fun _ ↦ by
      apply Bicategory.Adj.hom₂_ext
      apply Cat.Hom₂.ext
      ext
      apply Over.OverMorphism.ext
      rfl)
    (fun _ ↦ by
      apply Bicategory.Adj.hom₂_ext
      apply Cat.Hom₂.ext
      ext
      apply Over.OverMorphism.ext
      rfl)

set_option maxHeartbeats 1000000 in
/-- Pullback between scheme slices, regarded as a pseudofunctor on the opposite category. -/
private noncomputable def overPullbackPseudofunctor :
    LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat.{u} := by
  let Q := overAdjPseudofunctor
  exact LocallyDiscrete.mkPseudofunctor
    (fun X ↦ (Q.obj ⟨X.unop⟩).obj)
    (fun f ↦ (Q.map f.unop.toLoc).r)
    (fun X ↦ Bicategory.Adj.rIso (Q.mapId ⟨X.unop⟩))
    (fun f g ↦ Bicategory.Adj.rIso (Q.mapComp g.unop.toLoc f.unop.toLoc))
    (fun f g h ↦ by
      have H := (congrArg (fun k ↦ k.τr)
        (Q.map₂_associator h.unop.toLoc g.unop.toLoc f.unop.toLoc)).symm
      convert H using 1 <;> rfl)
    (fun {X _} f ↦ by
      have H := congrArg (fun k ↦ k.τr) (Q.map₂_right_unitor f.unop.toLoc)
      let A := Bicategory.Adj.rIso (Q.mapComp f.unop.toLoc
        (𝟙 (⟨X.unop⟩ : LocallyDiscrete Scheme.{u})))
      let B := Bicategory.whiskerRightIso (Bicategory.Adj.rIso (Q.mapId ⟨X.unop⟩))
        (Q.map f.unop.toLoc).r
      let C := λ_ (Q.map f.unop.toLoc).r
      let Fiso := A ≪≫ B ≪≫ C
      let E := Bicategory.Adj.rIso (Q.map₂Iso (ρ_ f.unop.toLoc))
      have hInv : Fiso.inv = E.inv := by
        change _ = (Q.map₂ (ρ_ f.unop.toLoc).hom).τr
        rw [H]
        rfl
      have hHom := (Iso.inv_eq_inv Fiso E).mp hInv
      convert hHom using 1 <;> rfl)

    (fun {_ Y} f ↦ by
      have H := congrArg (fun k ↦ k.τr) (Q.map₂_left_unitor f.unop.toLoc)
      let A := Bicategory.Adj.rIso (Q.mapComp
        (𝟙 (⟨Y.unop⟩ : LocallyDiscrete Scheme.{u})) f.unop.toLoc)
      let B := Bicategory.whiskerLeftIso (Q.map f.unop.toLoc).r
        (Bicategory.Adj.rIso (Q.mapId ⟨Y.unop⟩))
      let C := ρ_ (Q.map f.unop.toLoc).r
      let Fiso := A ≪≫ B ≪≫ C
      let E := Bicategory.Adj.rIso (Q.map₂Iso (λ_ f.unop.toLoc))
      have hInv : Fiso.inv = E.inv := by
        change _ = (Q.map₂ (λ_ f.unop.toLoc).hom).τr
        rw [H]
        rfl
      have hHom := (Iso.inv_eq_inv Fiso E).mp hInv
      convert hHom using 1 <;> rfl)

section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The object component of postcomposition by the pullback pseudofunctor. -/
private noncomputable def postcomposeApp
    {I : Type u} [Category I]
    {F G : LocallyDiscrete I ⥤ᵖ LocallyDiscrete Scheme.{u}ᵒᵖ}
    (η : Pseudofunctor.StrongTrans F G) (i : LocallyDiscrete I) :
    (F.comp overPullbackPseudofunctor).obj i ⟶
      (G.comp overPullbackPseudofunctor).obj i :=
  overPullbackPseudofunctor.map (η.app i)

/-- The naturality isomorphism obtained by applying the pullback pseudofunctor to a strong
transformation. -/
private noncomputable def postcomposeNaturality
    {I : Type u} [Category I]
    {F G : LocallyDiscrete I ⥤ᵖ LocallyDiscrete Scheme.{u}ᵒᵖ}
    (η : Pseudofunctor.StrongTrans F G) {i j : LocallyDiscrete I} (f : i ⟶ j) :
    (F.comp overPullbackPseudofunctor).map f ≫ postcomposeApp η j ≅
      postcomposeApp η i ≫ (G.comp overPullbackPseudofunctor).map f :=
  (overPullbackPseudofunctor.mapComp (F.map f) (η.app j)).symm ≪≫
    overPullbackPseudofunctor.map₂Iso (η.naturality f) ≪≫
      overPullbackPseudofunctor.mapComp (η.app i) (G.map f)

/-- Postcomposition of a strong transformation by the pullback pseudofunctor. -/
private noncomputable def postcompose
    {I : Type u} [Category I]
    {F G : LocallyDiscrete I ⥤ᵖ LocallyDiscrete Scheme.{u}ᵒᵖ}
    (η : Pseudofunctor.StrongTrans F G) :
    Pseudofunctor.StrongTrans
      (F.comp overPullbackPseudofunctor) (G.comp overPullbackPseudofunctor) where
  app i := postcomposeApp η i
  naturality f := postcomposeNaturality η f
  naturality_naturality := fun {a b f g} γ ↦ by
    have hfg : f = g := LocallyDiscrete.eq_of_hom γ
    subst g
    have hγ : γ = 𝟙 f := Subsingleton.elim _ _
    subst γ
    simp
  naturality_id := fun a ↦ by
    unfold postcomposeNaturality postcomposeApp
    rw [Pseudofunctor.comp_mapId, Pseudofunctor.comp_mapId]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      PrelaxFunctor.mapFunctor_map]
    simp only [Category.assoc]
    change (overPullbackPseudofunctor.mapComp (F.map (𝟙 a)) (η.app a)).inv ≫
        overPullbackPseudofunctor.map₂ ((η.naturality (𝟙 a)).hom) ≫
        (overPullbackPseudofunctor.mapComp (η.app a) (G.map (𝟙 a))).hom ≫
        overPullbackPseudofunctor.map (η.app a) ◁
          (overPullbackPseudofunctor.map₂ (G.mapId a).hom ≫
            (overPullbackPseudofunctor.mapId (G.obj a)).hom) = _
    rw [η.naturality_id_hom a]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, PrelaxFunctor.map₂_comp,
      Pseudofunctor.map₂_whisker_left, Pseudofunctor.map₂_whisker_right,
      Pseudofunctor.map₂_left_unitor]
    simp only [← Bicategory.whiskerLeft_comp]
    rw [overPullbackPseudofunctor.map₂_iso_inv]
    simp only [overPullbackPseudofunctor.map₂_right_unitor]
    have hinner :
        overPullbackPseudofunctor.map₂ (G.mapId a).inv ≫
            overPullbackPseudofunctor.map₂ (G.mapId a).hom ≫
            (overPullbackPseudofunctor.mapId (G.obj a)).hom =
          (overPullbackPseudofunctor.mapId (G.obj a)).hom := by
      rw [← Category.assoc, ← overPullbackPseudofunctor.map₂_comp,
        Iso.inv_hom_id, overPullbackPseudofunctor.map₂_id, Category.id_comp]
    rw [hinner]
    have houter :
        inv ((overPullbackPseudofunctor.mapComp (η.app a) (𝟙 (G.obj a))).hom ≫
            overPullbackPseudofunctor.map (η.app a) ◁
              (overPullbackPseudofunctor.mapId (G.obj a)).hom ≫
            (ρ_ (overPullbackPseudofunctor.map (η.app a))).hom) ≫
          (overPullbackPseudofunctor.mapComp (η.app a) (𝟙 (G.obj a))).hom ≫
          overPullbackPseudofunctor.map (η.app a) ◁
            (overPullbackPseudofunctor.mapId (G.obj a)).hom =
        (ρ_ (overPullbackPseudofunctor.map (η.app a))).inv := by
      rw [← cancel_mono (ρ_ (overPullbackPseudofunctor.map (η.app a))).hom]
      simpa only [Category.assoc, Category.comp_id, Iso.inv_hom_id] using
        IsIso.inv_hom_id_assoc
          ((overPullbackPseudofunctor.mapComp (η.app a) (𝟙 (G.obj a))).hom ≫
            overPullbackPseudofunctor.map (η.app a) ◁
              (overPullbackPseudofunctor.mapId (G.obj a)).hom ≫
            (ρ_ (overPullbackPseudofunctor.map (η.app a))).hom)
          (𝟙 (overPullbackPseudofunctor.map (η.app a)))
    rw [houter]
    have hprefix :
        overPullbackPseudofunctor.map₂ (F.mapId a).hom ▷
              overPullbackPseudofunctor.map (η.app a) ≫
            (overPullbackPseudofunctor.mapId (F.obj a)).hom ▷
              overPullbackPseudofunctor.map (η.app a) =
          (overPullbackPseudofunctor.map₂ (F.mapId a).hom ≫
              (overPullbackPseudofunctor.mapId (F.obj a)).hom) ▷
            overPullbackPseudofunctor.map (η.app a) := by
      rw [Bicategory.comp_whiskerRight]
    rw [← Category.assoc, hprefix]
  naturality_comp := fun f g ↦ by
    unfold postcomposeNaturality postcomposeApp
    rw [Pseudofunctor.comp_mapComp, Pseudofunctor.comp_mapComp]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      PrelaxFunctor.mapFunctor_map, Category.assoc]
    rw [η.naturality_comp_hom f g]
    simp only [Pseudofunctor.comp_toPrelaxFunctor,
      PrelaxFunctor.comp_toPrelaxFunctorStruct, PrelaxFunctorStruct.comp_toPrefunctor,
      Prefunctor.comp_obj, Prefunctor.comp_map, PrelaxFunctor.map₂_comp,
      Pseudofunctor.map₂_whisker_right, Pseudofunctor.map₂_associator,
      Pseudofunctor.map₂_whisker_left, Category.assoc, Iso.inv_hom_id_assoc,
      Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight]
    have htailInner :
        overPullbackPseudofunctor.map₂ (G.mapComp f g).inv ≫
            overPullbackPseudofunctor.map₂ (G.mapComp f g).hom ≫
            (overPullbackPseudofunctor.mapComp (G.map f) (G.map g)).hom =
          (overPullbackPseudofunctor.mapComp (G.map f) (G.map g)).hom := by
      rw [← Category.assoc, ← overPullbackPseudofunctor.map₂_comp,
        Iso.inv_hom_id, overPullbackPseudofunctor.map₂_id, Category.id_comp]
    have htail :
        overPullbackPseudofunctor.map (η.app _) ◁
              (overPullbackPseudofunctor.mapComp (G.map f) (G.map g)).inv ≫
            overPullbackPseudofunctor.map (η.app _) ◁
              overPullbackPseudofunctor.map₂ (G.mapComp f g).inv ≫
            overPullbackPseudofunctor.map (η.app _) ◁
              overPullbackPseudofunctor.map₂ (G.mapComp f g).hom ≫
            overPullbackPseudofunctor.map (η.app _) ◁
              (overPullbackPseudofunctor.mapComp (G.map f) (G.map g)).hom = 𝟙 _ := by
      rw [← Bicategory.whiskerLeft_comp, ← Bicategory.whiskerLeft_comp,
        ← Bicategory.whiskerLeft_comp]
      rw [htailInner, Iso.inv_hom_id, Bicategory.whiskerLeft_id]
    rw [htail, Category.comp_id]
    have hmiddle :
        (overPullbackPseudofunctor.mapComp (F.map f) (η.app _ ≫ G.map g)).inv ≫
            overPullbackPseudofunctor.map₂
              (α_ (F.map f) (η.app _) (G.map g)).inv ≫
            (overPullbackPseudofunctor.mapComp (F.map f ≫ η.app _) (G.map g)).hom =
          overPullbackPseudofunctor.map (F.map f) ◁
                (overPullbackPseudofunctor.mapComp (η.app _) (G.map g)).hom ≫
            (α_ (overPullbackPseudofunctor.map (F.map f))
              (overPullbackPseudofunctor.map (η.app _))
              (overPullbackPseudofunctor.map (G.map g))).inv ≫
            (overPullbackPseudofunctor.mapComp (F.map f) (η.app _)).inv ▷
              overPullbackPseudofunctor.map (G.map g) := by
      apply (Iso.inv_comp_eq
        (overPullbackPseudofunctor.mapComp (F.map f) (η.app _ ≫ G.map g))).mpr
      rw [← PrelaxFunctor.map₂Iso_inv]
      apply (Iso.inv_comp_eq (overPullbackPseudofunctor.map₂Iso
        (α_ (F.map f) (η.app _) (G.map g)))).mpr
      simp only [← Category.assoc]
      apply (Iso.eq_comp_inv (Bicategory.whiskerRightIso
        (overPullbackPseudofunctor.mapComp (F.map f) (η.app _))
        (overPullbackPseudofunctor.map (G.map g)))).mpr
      simpa only [Bicategory.whiskerRightIso, PrelaxFunctor.map₂Iso_hom,
        Category.assoc] using overPullbackPseudofunctor.mapComp_assoc_left_hom
          (F.map f) (η.app _) (G.map g)
    slice_lhs 6 8 => rw [hmiddle]
    simp only [Category.assoc]

/-- The Cat-valued pseudofunctor whose fiber at a stage is the category of quasi-compact,
quasi-separated schemes locally of finite presentation over that stage and whose arrow action is
affine base change. -/
@[no_expose]
noncomputable def pseudofunctor
    {I : Type u} [Preorder I] (D : OrderDual I ⥤ Scheme.{u})
    [hD : ∀ {i j : I} (hij : i ≤ j), IsAffineHom (D.map (homOfLE hij))] :
    LocallyDiscrete I ⥤ᵖ Cat.{u} := by
  let E : I ⥤ Scheme.{u}ᵒᵖ :=
    { obj := fun i ↦ Opposite.op (D.obj (show OrderDual I from i))
      map := fun f ↦ (D.map (homOfLE (leOfHom f))).op
      map_id := fun i ↦ by
        apply Quiver.Hom.unop_inj
        simp
      map_comp := fun f g ↦ by
        rw [← op_comp, ← D.map_comp]
        congr }
  let F := E.toPseudofunctor.comp overPullbackPseudofunctor
  let P : F.ObjectProperty :=
    { prop := fun i ↦
        locallyFinitePresentationProperty (D.obj (show OrderDual I from i.as)) }
  -- Local instance justification (proof-local temporary data): `fullsubcategory` consumes the
  -- closure proof only while restricting the pullback pseudofunctor to the chosen fibers.
  letI : P.IsClosedUnderMapObj :=
    { map_obj := fun {X Y} {M} hM f ↦ by
        -- Local instance justification (proof-local temporary data): install the supplied
        -- affine-transition proof at the arrow represented by this locally discrete morphism.
        letI : IsAffineHom (D.map (homOfLE (leOfHom f.as))) := hD _
        change locallyFinitePresentationProperty (D.obj (show OrderDual I from Y.as))
          ((Over.pullback (D.map (homOfLE (leOfHom f.as)))).obj M)
        exact baseChange_mem (D.map (homOfLE (leOfHom f.as))) M hM }
  exact P.fullsubcategory

/-- The morphisms in the Grothendieck construction whose component in the target fiber is an
isomorphism. -/
def transitionMorphisms
    {I : Type u} [Preorder I] (D : OrderDual I ⥤ Scheme.{u})
    [∀ {i j : I} (hij : i ≤ j), IsAffineHom (D.map (homOfLE hij))] :
    MorphismProperty (Pseudofunctor.Grothendieck (pseudofunctor D)) :=
  fun _ _ f ↦ IsIso f.fiber

/-- The pseudocolimit of the stage categories, modeled as the localization of their
Grothendieck construction at transition morphisms. -/
abbrev Colimit
    {I : Type u} [Preorder I] (D : OrderDual I ⥤ Scheme.{u})
    [∀ {i j : I} (hij : i ≤ j), IsAffineHom (D.map (homOfLE hij))] :=
  (transitionMorphisms D).Localization

set_option maxHeartbeats 10000000 in
/-- The strong transformation defined by the projections of a cone, contravariantly viewed on
the associated diagram of opposite schemes. -/
private noncomputable def coneStrongTrans
    {I : Type u} [Preorder I] (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) :
    let E : I ⥤ Scheme.{u}ᵒᵖ :=
      { obj := fun i ↦ Opposite.op (D.obj (show OrderDual I from i))
        map := fun f ↦ (D.map (homOfLE (leOfHom f))).op
        map_id := fun i ↦ by
          apply Quiver.Hom.unop_inj
          simp
        map_comp := fun f g ↦ by
          rw [← op_comp, ← D.map_comp]
          congr }
    let K : I ⥤ Scheme.{u}ᵒᵖ := (Functor.const I).obj (Opposite.op c.pt)
    Pseudofunctor.StrongTrans E.toPseudofunctor K.toPseudofunctor := by
  dsimp only
  let E : I ⥤ Scheme.{u}ᵒᵖ :=
    { obj := fun i ↦ Opposite.op (D.obj (show OrderDual I from i))
      map := fun f ↦ (D.map (homOfLE (leOfHom f))).op
      map_id := fun i ↦ by
        apply Quiver.Hom.unop_inj
        simp
      map_comp := fun f g ↦ by
        rw [← op_comp, ← D.map_comp]
        congr }
  let K : I ⥤ Scheme.{u}ᵒᵖ := (Functor.const I).obj (Opposite.op c.pt)
  let η : E ⟶ K :=
    { app := fun i ↦ (c.π.app (show OrderDual I from i)).op
      naturality := fun {i j} f ↦ by
        apply Quiver.Hom.unop_inj
        change c.π.app (show OrderDual I from j) ≫ D.map (homOfLE (leOfHom f)) =
          𝟙 c.pt ≫ c.π.app (show OrderDual I from i)
        rw [Category.id_comp]
        exact c.w (homOfLE (leOfHom f)) }
  exact
    { app := fun i ↦ (η.app i.as).toLoc
      naturality := fun {i j} f ↦ eqToIso (by
        apply Discrete.ext
        exact η.naturality f.as) }

set_option maxHeartbeats 10000000 in
/-- Base change along the projections of an affine-transition limit, before passing to the
localization of the Grothendieck construction. -/
@[no_expose]
noncomputable def toLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [hD : ∀ {i j : I} (hij : i ≤ j), IsAffineHom (D.map (homOfLE hij))] :
    Pseudofunctor.Grothendieck (pseudofunctor D) ⥤ LocallyFinitePresentation c.pt := by
  -- Local instance justification (proof-local temporary data): reindex the supplied affine
  -- transition proofs along arbitrary arrows in the opposite preorder.
  letI : ∀ {i j : OrderDual I} (f : i ⟶ j), IsAffineHom (D.map f) := fun {i j} f ↦ by
    let hij := leOfHom f
    have hf : f = homOfLE hij := Subsingleton.elim _ _
    rw [hf]
    exact hD hij
  -- Local instance justification (proof-local temporary data): affine limit projections are
  -- needed only to form the displayed base-change functors.
  letI : ∀ i : I, IsAffineHom (c.π.app (show OrderDual I from i)) :=
    fun i ↦ isAffineHom_π_app D c hc (show OrderDual I from i)
  let E : I ⥤ Scheme.{u}ᵒᵖ :=
    { obj := fun i ↦ Opposite.op (D.obj (show OrderDual I from i))
      map := fun f ↦ (D.map (homOfLE (leOfHom f))).op
      map_id := fun i ↦ by
        apply Quiver.Hom.unop_inj
        simp
      map_comp := fun f g ↦ by
        rw [← op_comp, ← D.map_comp]
        congr }
  let K : I ⥤ Scheme.{u}ᵒᵖ := (Functor.const I).obj (Opposite.op c.pt)
  let H := E.toPseudofunctor.comp overPullbackPseudofunctor
  let P : H.ObjectProperty :=
    { prop := fun i ↦
        locallyFinitePresentationProperty (D.obj (show OrderDual I from i.as)) }
  -- Local instance justification (proof-local temporary data): this identifies the already
  -- defined restricted stage pseudofunctor while constructing its comparison functor.
  letI : P.IsClosedUnderMapObj :=
    { map_obj := fun {X Y} {M} hM f ↦ by
        -- Local instance justification (proof-local temporary data): unpack the supplied
        -- affine-transition hypothesis only for this base-change membership proof.
        letI : IsAffineHom (D.map (homOfLE (leOfHom f.as))) := hD _
        change locallyFinitePresentationProperty (D.obj (show OrderDual I from Y.as))
          ((Over.pullback (D.map (homOfLE (leOfHom f.as)))).obj M)
        exact baseChange_mem (D.map (homOfLE (leOfHom f.as))) M hM }
  change Pseudofunctor.Grothendieck P.fullsubcategory ⥤ LocallyFinitePresentation c.pt
  let G := K.toPseudofunctor.comp overPullbackPseudofunctor
  let τ : Pseudofunctor.StrongTrans H G :=
    postcompose (coneStrongTrans D c)
  let obj (X : Pseudofunctor.Grothendieck P.fullsubcategory) : Over c.pt :=
    (Over.pullback (c.π.app (show OrderDual I from X.base))).obj X.fiber.obj
  let map (X Y : Pseudofunctor.Grothendieck P.fullsubcategory) (f : X ⟶ Y) :
      obj X ⟶ obj Y :=
    (G.mapId ⟨X.base⟩).inv.toNatTrans.app
        ((τ.app ⟨X.base⟩).toFunctor.obj X.fiber.obj) ≫
      (τ.naturality (a := ⟨X.base⟩) (b := ⟨Y.base⟩)
        f.base.toLoc).inv.toNatTrans.app X.fiber.obj ≫
        (τ.app ⟨Y.base⟩).toFunctor.map f.fiber.hom
  let F : Pseudofunctor.Grothendieck P.fullsubcategory ⥤ Over c.pt :=
    { obj := obj
      map := fun {X Y} f ↦ map X Y f
      map_id := fun X ↦ by
        change map X X (𝟙 X) = 𝟙 (obj X)
        dsimp only [map]
        simp only [Pseudofunctor.Grothendieck.categoryStruct_id_base,
          Quiver.Hom.id_toLoc]
        rw [Pseudofunctor.StrongTrans.naturality_id_inv_app]
        simp [Pseudofunctor.ObjectProperty.mapId_hom_app, G, K, H, E,
          PrelaxFunctor.map₂_eqToHom,
          ← Cat.Hom.toNatIso_inv, ← Cat.Hom.toNatIso_hom, ← Functor.map_comp]
        rfl
      map_comp := sorry }
  exact (locallyFinitePresentationProperty c.pt).lift F (fun X ↦
    baseChange_mem (c.π.app (show OrderDual I from X.base)) X.fiber.obj X.fiber.property)

end

/-- Base change to the limit sends every transition morphism in the Grothendieck construction to
an isomorphism. -/
theorem toLimit_inverts
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [hD : ∀ {i j : I} (hij : i ≤ j), IsAffineHom (D.map (homOfLE hij))] :
    (transitionMorphisms D).IsInvertedBy (toLimit D c hc) := by
  intro X Y f hf
  rw [← isIso_iff_of_reflects_iso _ (inclusion c.pt)]
  rw [← isIso_iff_of_reflects_iso _ (Over.forget c.pt)]
  -- Local instance justification (proof-local temporary data): expose the fiber isomorphism only while proving that its explicitly mapped composite is invertible.
  letI : IsIso f.fiber.hom :=
    (ObjectProperty.isIso_hom_iff f.fiber).mpr hf
  dsimp [toLimit]
  change IsIso (_ ≫ _ ≫ _)
  apply IsIso.comp_isIso'
  · let G := ((Functor.const I).obj (Opposite.op c.pt)).toPseudofunctor.comp
      overPullbackPseudofunctor
    let e := (Cat.Hom.toNatIso (G.mapId ⟨X.base⟩)).symm.app
        (((postcompose (coneStrongTrans D c)).app ⟨X.base⟩).toFunctor.obj
          X.fiber.obj)
    change IsIso ((Over.forget c.pt).map e.hom)
    exact { out := ⟨(Over.forget c.pt).map e.inv,
      ((Over.forget c.pt).map_comp e.hom e.inv).symm.trans
        (((Over.forget c.pt).congr_map e.hom_inv_id).trans
          ((Over.forget c.pt).map_id _)),
      ((Over.forget c.pt).map_comp e.inv e.hom).symm.trans
        (((Over.forget c.pt).congr_map e.inv_hom_id).trans
          ((Over.forget c.pt).map_id _))⟩ }
  · apply IsIso.comp_isIso'
    · let e := (Cat.Hom.toNatIso
        ((postcompose (coneStrongTrans D c)).naturality f.base.toLoc)).symm.app
          X.fiber.obj
      change IsIso ((Over.forget c.pt).map e.hom)
      exact { out := ⟨(Over.forget c.pt).map e.inv,
        ((Over.forget c.pt).map_comp e.hom e.inv).symm.trans
          (((Over.forget c.pt).congr_map e.hom_inv_id).trans
            ((Over.forget c.pt).map_id _)),
        ((Over.forget c.pt).map_comp e.inv e.hom).symm.trans
          (((Over.forget c.pt).congr_map e.inv_hom_id).trans
            ((Over.forget c.pt).map_id _))⟩ }
    · change IsIso ((Over.forget c.pt).map
        (((postcompose (coneStrongTrans D c)).app
          ⟨Y.base⟩).toFunctor.map f.fiber.hom))
      exact Functor.map_isIso _ _

/-- The comparison from the localized colimit of the stage categories to the category over the
limit scheme, induced by base change along the limit projections. -/
noncomputable def comparison
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (hij : i ≤ j), IsAffineHom (D.map (homOfLE hij))] :
    Colimit D ⥤ LocallyFinitePresentation c.pt :=
  CategoryTheory.Localization.Construction.lift (toLimit D c hc)
    (toLimit_inverts D c hc)

/-- An object over a directed affine limit that is quasi-compact, quasi-separated, and locally of
finite presentation descends to some stage. -/
@[stacks 0EY1]
theorem stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (X : Over c.pt) (hX : locallyFinitePresentationProperty c.pt X) :
    ∃ (i : I) (Xi : Over (D.obj i)),
      locallyFinitePresentationProperty (D.obj i) Xi ∧
        Nonempty ((Over.pullback (c.π.app i)).obj Xi ≅ X) := sorry

/-- A morphism over a directed affine limit between two objects obtained by base change descends
after passing to a later stage. -/
@[stacks 0EY1]
theorem homStage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (i : I) (X Y : Over (D.obj i))
    (hX : locallyFinitePresentationProperty (D.obj i) X)
    (hY : locallyFinitePresentationProperty (D.obj i) Y)
    (f : (Over.pullback (c.π.app i)).obj X ⟶ (Over.pullback (c.π.app i)).obj Y) :
    ∃ (i' : I) (hii' : i ≤ i')
      (hcomp : c.π.app i' ≫ D.map (homOfLE hii') = c.π.app i)
      (g : (Over.pullback (D.map (homOfLE hii'))).obj X ⟶
        (Over.pullback (D.map (homOfLE hii'))).obj Y),
      (Over.pullbackComp (c.π.app i') (D.map (homOfLE hii'))).hom.app X ≫
          (Over.pullback (c.π.app i')).map g ≫
        (Over.pullbackComp (c.π.app i') (D.map (homOfLE hii'))).inv.app Y =
        eqToHom (congrArg (fun F : Over (D.obj i) ⥤ Over c.pt ↦ F.obj X)
          (Over.pullback.congr_simp (c.π.app i' ≫ D.map (homOfLE hii'))
            (c.π.app i) hcomp)) ≫
          f ≫
        eqToHom (Eq.symm (congrArg (fun F : Over (D.obj i) ⥤ Over c.pt ↦ F.obj Y)
          (Over.pullback.congr_simp (c.π.app i' ≫ D.map (homOfLE hii'))
            (c.π.app i) hcomp))) := sorry

/-- Two stage morphisms that agree after base change to a directed affine limit already agree
after base change to some later stage. -/
@[stacks 0EY1]
theorem eqStage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (i : I) (X Y : Over (D.obj i))
    (hX : locallyFinitePresentationProperty (D.obj i) X)
    (hY : locallyFinitePresentationProperty (D.obj i) Y)
    (f g : X ⟶ Y)
    (hfg : (Over.pullback (c.π.app i)).map f = (Over.pullback (c.π.app i)).map g) :
    ∃ (i' : I) (hii' : i ≤ i'),
      (Over.pullback (D.map (homOfLE hii'))).map f =
        (Over.pullback (D.map (homOfLE hii'))).map g := sorry

/-- The base-change comparison from the localized colimit of quasi-compact, quasi-separated,
locally finitely presented schemes over the stages to the corresponding category over the limit
scheme is an equivalence. -/
@[stacks 0EY1]
theorem comparison_isEquivalence
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (hij : i ≤ j), IsAffineHom (D.map (homOfLE hij))] :
    (comparison D c hc).IsEquivalence := sorry

attribute [instance] comparison_isEquivalence

end Descent

end LocallyFinitePresentation

end AlgebraicGeometry.Scheme.Over.Qcqs
