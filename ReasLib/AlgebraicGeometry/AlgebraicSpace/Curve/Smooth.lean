/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.OverField
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.Topology.KrullDimension.Equidimensional

/-!
# Smooth families of curves

Smoothness and smoothness of relative dimension one are represented by opens
of the base of a curve family under arbitrary scheme base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The object property of families of curves with smooth structure morphism. -/
def smooth (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ AlgebraicSpace.Smooth (hom P)

/-- Membership in `smooth` is smoothness of the structure morphism. -/
theorem smooth_iff {S : Scheme.{u}} (P : Obj S) :
    smooth S P ↔ AlgebraicSpace.Smooth (hom P) := Iff.rfl

/-- Smoothness of families of curves is invariant under isomorphisms. -/
instance instIsClosedUnderIsomorphisms_smooth (S : Scheme.{u}) :
    (smooth S).IsClosedUnderIsomorphisms := by
  constructor
  intro P Q e hP
  let F : Obj S ⥤ Spaces S :=
    (relativeDimensionLE S 1).ι ⋙ (fpFlatProper S).ι ⋙
      wideSubcategoryInclusion _ ⋙ (finiteType S).ι
  let e' := F.mapIso e
  let eX : (space P).functorOfPoints ≅ (space Q).functorOfPoints :=
    { hom := e'.hom.left
      inv := e'.inv.left
      hom_inv_id := congrArg (fun f : F.obj P ⟶ F.obj P => f.left) e'.hom_inv_id
      inv_hom_id := congrArg (fun f : F.obj Q ⟶ F.obj Q => f.left) e'.inv_hom_id }
  let eY := yoneda.mapIso ((Comma.snd _ _).mapIso e')
  letI : IsIso (C := (Over S)ᵒᵖ ⥤ Type u) eX.inv :=
    ⟨⟨eX.hom, eX.inv_hom_id, eX.hom_inv_id⟩⟩
  refine ⟨?_⟩
  intro U V a b h ha hb w
  apply hP.of_etale (a ≫ eX.inv) (b ≫ eY.inv) h
  · exact (MorphismProperty.cancel_right_of_respectsIso
      (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a eX.inv).mpr ha
  · exact (MorphismProperty.cancel_right_of_respectsIso
      (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b eY.inv).mpr hb
  · calc
      (a ≫ eX.inv) ≫ hom P = a ≫ (hom Q ≫ eY.inv) := by
        have he : eX.inv ≫ hom P = hom Q ≫ eY.inv := e'.inv.w
        rw [Category.assoc, he]
        rfl
      _ = _ := by rw [← Category.assoc a, w, Category.assoc]; rfl

/-- The object property of families of curves whose structure morphism is
smooth of relative dimension one. -/
def smoothDim1 (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ AlgebraicSpace.Smooth (hom P) ∧ RelativeDimension (hom P) 1

/-- Membership in `smoothDim1` is smoothness and exact relative dimension one
of the structure morphism. -/
theorem smoothDim1_iff {S : Scheme.{u}} (P : Obj S) :
    smoothDim1 S P ↔
      AlgebraicSpace.Smooth (hom P) ∧ RelativeDimension (hom P) 1 := Iff.rfl

/-- Smoothness of relative dimension one for families of curves is invariant
under isomorphisms. -/
instance instIsClosedUnderIsomorphisms_smoothDim1 (S : Scheme.{u}) :
    (smoothDim1 S).IsClosedUnderIsomorphisms := by
  constructor
  intro P Q e hP
  refine ⟨(smooth S).prop_of_iso e hP.1, ?_⟩
  let F : Obj S ⥤ Spaces S :=
    (relativeDimensionLE S 1).ι ⋙ (fpFlatProper S).ι ⋙
      wideSubcategoryInclusion _ ⋙ (finiteType S).ι
  let e' := F.mapIso e
  let eX : (space P).functorOfPoints ≅ (space Q).functorOfPoints :=
    { hom := e'.hom.left
      inv := e'.inv.left
      hom_inv_id := congrArg (fun f : F.obj P ⟶ F.obj P => f.left) e'.hom_inv_id
      inv_hom_id := congrArg (fun f : F.obj Q ⟶ F.obj Q => f.left) e'.inv_hom_id }
  let eY := yoneda.mapIso ((Comma.snd _ _).mapIso e')
  letI : IsIso (C := (Over S)ᵒᵖ ⥤ Type u) eX.hom :=
    ⟨⟨eX.inv, eX.hom_inv_id, eX.inv_hom_id⟩⟩
  constructor
  intro x
  obtain ⟨U, V, a, b, h, u, ha, hb, w, hx, hu⟩ :=
    hP.2.relativeDimensionAt (Points.map e'.inv.left x)
  refine ⟨U, V, a ≫ eX.hom, b ≫ eY.hom, h, u, ?_, ?_, ?_, ?_, hu⟩
  · exact (MorphismProperty.cancel_right_of_respectsIso
      (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a eX.hom).mpr ha
  · exact (MorphismProperty.cancel_right_of_respectsIso
      (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b eY.hom).mpr hb
  · have he : e'.hom.left ≫ hom Q =
        hom P ≫ (ofOverFunctor S).map e'.hom.right := e'.hom.w
    change (a ≫ e'.hom.left) ≫ hom Q =
      (ofOverMap h ≫ b) ≫ (ofOverFunctor S).map e'.hom.right
    calc
      (a ≫ e'.hom.left) ≫ hom Q = a ≫ (e'.hom.left ≫ hom Q) := Category.assoc _ _ _
      _ = a ≫ (hom P ≫ (ofOverFunctor S).map e'.hom.right) :=
        congrArg (fun t : space P ⟶ ofOver (base Q) => a ≫ t) he
      _ = (a ≫ hom P) ≫ (ofOverFunctor S).map e'.hom.right :=
        (Category.assoc _ _ _).symm
      _ = _ := congrArg
        (fun t : ofOver U ⟶ ofOver (base P) => t ≫ (ofOverFunctor S).map e'.hom.right) w
  · calc
      Points.map (a ≫ e'.hom.left) (ofOver.pointsEquiv U u) =
          Points.map e'.hom.left (Points.map a (ofOver.pointsEquiv U u)) := by
        exact Quotient.inductionOn (ofOver.pointsEquiv U u) (fun q => rfl)
      _ = Points.map e'.hom.left (Points.map e'.inv.left x) := congrArg _ hx
      _ = Points.map (e'.inv.left ≫ e'.hom.left) x := by
        exact Quotient.inductionOn x (fun q => rfl)
      _ = Points.map (𝟙 (space Q)) x := by
        have he : e'.inv.left ≫ e'.hom.left = 𝟙 (space Q) :=
          congrArg (fun f : F.obj Q ⟶ F.obj Q => f.left) e'.inv_hom_id
        exact congrArg (fun f : space Q ⟶ space Q => Points.map f x) he
      _ = x := Quotient.inductionOn x (fun q => rfl)

/-- A smooth family of curves of relative dimension one is smooth. -/
theorem smoothDim1_le_smooth {S : Scheme.{u}} (P : Obj S) :
    smoothDim1 S P → smooth S P := fun h => h.1

/-- For every family of curves, an open of its base represents smoothness of
its pullback under every scheme base change. -/
theorem exists_smooth_open {S : Scheme.{u}} (P : Obj S) :
    ∃ U : (base P).left.Opens, ∀ T : Over (base P).left,
      AlgebraicSpace.Smooth
          (pullbackAlongScheme.snd (hom P)
            (ofOverHomMk (σK := T.hom ≫ (base P).hom)
              (σL := (base P).hom) T.hom rfl)) ↔
        Set.range T.hom ⊆ U :=
  sorry

/-- For every family of curves, an open of its base represents smoothness of
relative dimension one of its pullback under every scheme base change. -/
theorem exists_smoothDim1_open {S : Scheme.{u}} (P : Obj S) :
    ∃ U : (base P).left.Opens, ∀ T : Over (base P).left,
      (AlgebraicSpace.Smooth
          (pullbackAlongScheme.snd (hom P)
            (ofOverHomMk (σK := T.hom ≫ (base P).hom)
              (σL := (base P).hom) T.hom rfl)) ∧
        RelativeDimension
          (pullbackAlongScheme.snd (hom P)
            (ofOverHomMk (σK := T.hom ≫ (base P).hom)
              (σL := (base P).hom) T.hom rfl)) 1) ↔
        Set.range T.hom ⊆ U :=
  sorry

/-- A proper scheme of dimension at most one over a field defines a smooth
curve family precisely when its structure morphism is smooth. -/
theorem classifying_factorsThrough_smooth_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    smooth (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      AlgebraicGeometry.Smooth X.hom := by
  let f : Over.mk X.hom ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k))) :=
    Over.homMk X.hom (Category.comp_id X.hom)
  change AlgebraicSpace.Smooth (ofOverMap f) ↔ _
  constructor
  · intro h
    exact h.of_etale (𝟙 _) (𝟙 _) f
      (ofOver_id_presheaf_etale _) (ofOver_id_presheaf_etale _) (by rfl)
  · intro hX
    letI := hX
    letI : MorphismProperty.IsMultiplicative @AlgebraicGeometry.Smooth :=
      { id_mem := fun A => inferInstance
        toIsStableUnderComposition := inferInstance }
    letI : MorphismProperty.HasOfPostcompProperty @AlgebraicGeometry.Smooth
        @AlgebraicGeometry.Etale := by
      rw [MorphismProperty.hasOfPostcompProperty_iff_le_diagonal]
      intro A B f hf
      letI := hf
      letI : AlgebraicGeometry.FormallyUnramified f :=
        { formallyUnramified_appLE := fun {_} hU {_} hV e =>
            (f.etale_appLE hU hV e).formallyUnramified }
      letI : AlgebraicGeometry.LocallyOfFiniteType f :=
        { finiteType_appLE := fun {_} hU {_} hV e =>
            RingHom.FiniteType.of_finitePresentation
              ((RingHom.Etale.iff_flat_and_formallyUnramified.mp
                (f.etale_appLE hU hV e)).2.2) }
      letI : AlgebraicGeometry.IsOpenImmersion (CategoryTheory.Limits.pullback.diagonal f) :=
        AlgebraicGeometry.FormallyUnramified.isOpenImmersion_diagonal f
      exact inferInstanceAs (AlgebraicGeometry.Smooth (CategoryTheory.Limits.pullback.diagonal f))
    constructor
    intro U V a b h ha hb w
    obtain ⟨a', rfl⟩ := yoneda.map_surjective a
    obtain ⟨b', rfl⟩ := yoneda.map_surjective b
    haveI : AlgebraicGeometry.Etale a'.left :=
      MorphismProperty.of_relative_map (F := yoneda)
        (P := MorphismProperty.over (@AlgebraicGeometry.Etale)) ha
    haveI : AlgebraicGeometry.Etale b'.left :=
      MorphismProperty.of_relative_map (F := yoneda)
        (P := MorphismProperty.over (@AlgebraicGeometry.Etale)) hb
    have hw : a' ≫ f = h ≫ b' :=
      yoneda.map_injective
        ((yoneda.map_comp a' f).trans (w.trans (yoneda.map_comp h b').symm))
    have hw' : a'.left ≫ X.hom = h.left ≫ b'.left :=
      congrArg (fun f : U ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k))) => f.left) hw
    apply MorphismProperty.of_postcomp @AlgebraicGeometry.Smooth h.left b'.left
      (inferInstance : AlgebraicGeometry.Etale b'.left)
    rw [← hw']
    exact MorphismProperty.comp_mem @AlgebraicGeometry.Smooth a'.left X.hom
      (inferInstance : AlgebraicGeometry.Smooth a'.left) hX

/-- A proper scheme of dimension at most one over a field defines a smooth
curve family of relative dimension one precisely when it is smooth and every
irreducible component has dimension one. -/
theorem smoothDim1_iff_scheme_components
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    smoothDim1 (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      AlgebraicGeometry.Smooth X.hom ∧
        ∀ Z : irreducibleComponents X.left, topologicalKrullDim Z = 1 :=
  sorry

open TopologicalSpace Order in
/-- Componentwise dimension bounds control the dimension of the whole space. -/
private theorem topologicalKrullDim_le_of_component_bounds
    {X : Type*} [TopologicalSpace X] {d : WithBot ℕ∞}
    (h : ∀ Z : irreducibleComponents X, topologicalKrullDim Z ≤ d) :
    topologicalKrullDim X ≤ d := by
  unfold topologicalKrullDim Order.krullDim
  refine iSup_le fun c => ?_
  obtain ⟨Z, hZ, hcZ⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible
      (c.last : Set X) c.last.isIrreducible
  have hsub (i : Fin (c.length + 1)) : (c i : Set X) ⊆ Z :=
    fun x hx => hcZ (c.monotone (Fin.le_last i) hx)
  let f (i : Fin (c.length + 1)) : IrreducibleCloseds Z :=
    { carrier := Subtype.val ⁻¹' (c i : Set X)
      isIrreducible' := by
        letI := Subtype.irreducibleSpace (c i).isIrreducible
        let j : ↥(c i : Set X) → Z := fun x => ⟨x.1, hsub i x.2⟩
        have hj : Continuous j := continuous_subtype_val.subtype_mk _
        have hm : j '' Set.univ = (Subtype.val ⁻¹' (c i : Set X) : Set Z) := by
          ext x
          constructor
          · rintro ⟨y, _, rfl⟩
            exact y.2
          · intro hx
            exact ⟨⟨x.1, hx⟩, Set.mem_univ _, rfl⟩
        rw [← hm]
        exact (IrreducibleSpace.isIrreducible_univ _).image j hj.continuousOn
      isClosed' := (c i).isClosed.preimage continuous_subtype_val }
  have hf : StrictMono f := by
    intro i j hij
    change (Subtype.val ⁻¹' (c i : Set X) : Set Z) ⊂ Subtype.val ⁻¹' (c j : Set X)
    refine ⟨Set.preimage_mono (c.monotone hij.le), ?_⟩
    intro H
    apply (c.strictMono hij).not_ge
    intro x hx
    exact H (show (⟨x, hsub j hx⟩ : Z) ∈ Subtype.val ⁻¹' (c j : Set X) from hx)
  exact (LTSeries.mk c.length f hf).length_le_krullDim.trans (h ⟨Z, hZ⟩)

/-- A nonempty proper scheme of dimension at most one over a field defines a
smooth curve family of relative dimension one precisely when it is smooth and
equidimensional of dimension one. -/
theorem classifying_factorsThrough_smoothDim1_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [Nonempty X.left] (hdim : topologicalKrullDim X.left ≤ 1) :
    smoothDim1 (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      AlgebraicGeometry.Smooth X.hom ∧
        TopologicalSpace.EquidimensionalSpace X.left ∧
        topologicalKrullDim X.left = 1 := by
  rw [smoothDim1_iff_scheme_components X hdim]
  constructor
  · rintro ⟨hs, hc⟩
    refine ⟨hs, ⟨fun Z W => (hc Z).trans (hc W).symm⟩, le_antisymm hdim ?_⟩
    obtain ⟨x⟩ := ‹Nonempty X.left›
    let Z : irreducibleComponents X.left :=
      ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
    rw [← hc Z]
    exact topologicalKrullDim_subspace_le _ _
  · rintro ⟨hs, he, hd⟩
    refine ⟨hs, fun Z => ?_⟩
    apply le_antisymm ((topologicalKrullDim_subspace_le _ _).trans hdim)
    rw [← hd]
    exact topologicalKrullDim_le_of_component_bounds
      fun W => le_of_eq (he.topologicalKrullDim_eq W Z)

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
