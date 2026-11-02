/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.GenericPoints

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of decent algebraic spaces with finitely many irreducible
components is birational if it bijects generic points of irreducible components
and induces an isomorphism of local rings at every source generic point. -/
@[mk_iff, stacks 0ACV]
class IsBirational {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) : Prop where
  /-- `|f|` bijects generic points of irreducible components. -/
  bijOn_genericPoints : Set.BijOn (Points.map f) (genericPoints X) (genericPoints Y)
  /-- The schematic-locus local ring map is an isomorphism at every generic
  point of `|X|`. -/
  isIso_stalkMap {x : Points X} : x ∈ genericPoints X → IsIsoStalkMapAt f x

namespace IsBirational

/-- A birational morphism bijects generic points of irreducible components. -/
theorem bijOn {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    {f : X ⟶ Y} [IsBirational f] :
    Set.BijOn (Points.map f) (genericPoints X) (genericPoints Y) :=
  IsBirational.bijOn_genericPoints

/-- A birational morphism induces an isomorphism of schematic-locus local rings
at every generic point of the source. -/
theorem isIsoStalkMap {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    {f : X ⟶ Y} [IsBirational f] {x : Points X} (hx : x ∈ genericPoints X) :
    IsIsoStalkMapAt f x :=
  IsBirational.isIso_stalkMap hx

/-- The two defining conditions of `IsBirational` may be supplied together. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    {f : X ⟶ Y} (h_bij : Set.BijOn (Points.map f) (genericPoints X) (genericPoints Y))
    (h_stalk : ∀ {x : Points X}, x ∈ genericPoints X → IsIsoStalkMapAt f x) :
    IsBirational f :=
  ⟨h_bij, h_stalk⟩

end IsBirational

/-- The identity morphism of a decent algebraic space with finitely many
irreducible components is birational. -/
instance instIsBirational_id {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] [HasFiniteIrreducibleComponents X] :
    IsBirational (𝟙 X) := by
  refine ⟨?_, ?_⟩
  · rw [show Points.map (𝟙 X) = id from funext Points.map_id]
    exact Set.bijOn_id (genericPoints X)
  · intro x hx
    obtain ⟨U, ι, hι, p, hp⟩ := genericPoints_subset_schematicLocus X hx
    obtain ⟨u, rfl⟩ := (ofOver.pointsEquiv U).surjective p
    refine ⟨U, U, ι, ι, 𝟙 U, u, hι, hι, ?_, hp, ?_⟩
    · change yoneda.map (𝟙 U) ≫ ι = ι ≫ 𝟙 X
      simp only [yoneda.map_id, Category.id_comp, Category.comp_id]
    · change IsIso ((𝟙 U.left : U.left ⟶ U.left).stalkMap u)
      rw [Scheme.Hom.stalkMap_id]
      exact CategoryTheory.IsIso.id _

set_option backward.isDefEq.respectTransparency false in
/-- The composite of birational morphisms of decent algebraic spaces with
finitely many irreducible components is birational. -/
instance instIsBirational_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] [IsDecent Z]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    [HasFiniteIrreducibleComponents Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsBirational f] [IsBirational g] :
    IsBirational (f ≫ g) := by
  refine ⟨?_, ?_⟩
  · rw [show Points.map (f ≫ g) = Points.map g ∘ Points.map f from
      funext (Points.map_comp f g)]
    exact (IsBirational.bijOn (f := g)).comp (IsBirational.bijOn (f := f))
  · intro x hx
    have hf := IsBirational.isIsoStalkMap (f := f) hx
    have hg := IsBirational.isIsoStalkMap (f := g)
      ((IsBirational.bijOn (f := f)).mapsTo hx)
    obtain ⟨U, _, ιU, _, _, u, hιU, _, _, hu, _⟩ := hf
    obtain ⟨V, W, ιV, ιW, ψ, v, hιV, hιW, hψ, hv, _⟩ := hg
    obtain ⟨P, pU, pV', hPB⟩ := hιV.presheaf.1 (ιU ≫ f)
    let pV : P ⟶ V := yoneda.preimage pV'
    have hpV : ofOverMap pV = pV' := yoneda.map_preimage pV'
    have hcomm : ofOverMap pV ≫ ιV = (ofOverMap pU ≫ ιU) ≫ f := by
      rw [hpV, Category.assoc]
      exact hPB.w
    haveI : AlgebraicGeometry.IsOpenImmersion pU.left :=
      hιV.presheaf.2 (ιU ≫ f) pV' pU hPB
    letI : MorphismProperty.IsStableUnderBaseChange
        (MorphismProperty.over (@AlgebraicGeometry.IsOpenImmersion) :
          MorphismProperty (Over S)) := by
      exact ⟨fun sq hj ↦ MorphismProperty.of_isPullback
        (P := @AlgebraicGeometry.IsOpenImmersion) (sq.map (Over.forget S)) hj⟩
    letI : MorphismProperty.IsStableUnderComposition
        (MorphismProperty.over (@AlgebraicGeometry.IsOpenImmersion) :
          MorphismProperty (Over S)) := by
      rw [MorphismProperty.over_eq_inverseImage]
      infer_instance
    have hpU : (MorphismProperty.over (@AlgebraicGeometry.IsOpenImmersion)).presheaf
        (ofOverMap pU) :=
      MorphismProperty.relative_map (F := yoneda)
        (P := MorphismProperty.over (@AlgebraicGeometry.IsOpenImmersion)) (f := pU)
        (show AlgebraicGeometry.IsOpenImmersion pU.left from inferInstance)
    haveI : IsOpenImmersion (ofOverMap pU ≫ ιU) :=
      ⟨MorphismProperty.comp_mem
        (MorphismProperty.over (@AlgebraicGeometry.IsOpenImmersion) :
          MorphismProperty (Over S)).presheaf (ofOverMap pU) ιU hpU hιU.presheaf⟩
    have hPB' : IsPullback (C := AlgebraicSpace S)
        (pV' : ofOver P ⟶ ofOver V) (ofOverMap pU) ιV (ιU ≫ f) := by
      refine IsPullback.of_isLimit (Limits.PullbackCone.IsLimit.mk
        (C := AlgebraicSpace S) (W := ofOver P) (X := ofOver V) (Y := ofOver U) (Z := Y)
        (fst := pV') (snd := ofOverMap pU) (f := ιV) (g := ιU ≫ f) hPB.w
        (fun c ↦ hPB.lift c.fst c.snd c.condition)
        (fun c ↦ hPB.lift_fst c.fst c.snd c.condition)
        (fun c ↦ hPB.lift_snd c.fst c.snd c.condition) ?_)
      intro c m hm₁ hm₂
      exact hPB.hom_ext (hm₁.trans (hPB.lift_fst _ _ _).symm)
        (hm₂.trans (hPB.lift_snd _ _ _).symm)
    obtain ⟨p, hpVpoint, hpUpoint⟩ := Points.exists_of_map_eq hPB'
      (ofOver.pointsEquiv V v) (ofOver.pointsEquiv U u)
      (by rw [hv, Points.map_comp, hu])
    obtain ⟨p, rfl⟩ := (ofOver.pointsEquiv P).surjective p
    have hxP : Points.map (ofOverMap pU ≫ ιU) (ofOver.pointsEquiv P p) = x := by
      rw [Points.map_comp, hpUpoint, hu]
    have hyP : Points.map ιV (ofOver.pointsEquiv V (pV.left p)) = Points.map f x := by
      rw [ofOver.pointsEquiv_naturality, hpV, hpVpoint, hv]
    haveI : IsIso (pV.left.stalkMap p) :=
      ((IsIsoStalkMapAt.spec f x).mp
        (IsBirational.isIsoStalkMap (f := f) hx)).2.2
        P V (ofOverMap pU ≫ ιU) ιV pV p inferInstance hιV hcomm hxP
    haveI : IsIso (ψ.left.stalkMap (pV.left p)) :=
      ((IsIsoStalkMapAt.spec g (Points.map f x)).mp
        (IsBirational.isIsoStalkMap (f := g)
          ((IsBirational.bijOn (f := f)).mapsTo hx))).2.2
        V W ιV ιW ψ (pV.left p) hιV hιW hψ hyP
    refine ⟨P, W, ofOverMap pU ≫ ιU, ιW, pV ≫ ψ, p,
      inferInstance, hιW, ?_, hxP, ?_⟩
    · rw [show ofOverMap (pV ≫ ψ) = ofOverMap pV ≫ ofOverMap ψ from yoneda.map_comp pV ψ,
        Category.assoc, hψ, ← Category.assoc, hcomm, Category.assoc]
    · change IsIso ((pV.left ≫ ψ.left).stalkMap p)
      rw [Scheme.Hom.stalkMap_comp]
      infer_instance

/-- A morphism of schemes over `S` is birational if and only if the induced
morphism of algebraic spaces is birational. -/
theorem isBirational_ofOverMap_iff {S : Scheme.{u}} {U V : Over S}
    [Finite (irreducibleComponents U.left)] [Finite (irreducibleComponents V.left)]
    (f : U ⟶ V) :
    IsBirational (ofOverMap f) ↔ AlgebraicGeometry.IsBirational f.left := by
  have hU (u : U.left) :
      ofOver.pointsEquiv U u ∈ genericPoints (ofOver U) ↔
        u ∈ _root_.genericPoints U.left := by
    rw [genericPoints_ofOver]
    constructor
    · rintro ⟨v, hv, hvu⟩
      exact (ofOver.pointsEquiv U).injective hvu ▸ hv
    · intro hu
      exact ⟨u, hu, rfl⟩
  have hV (v : V.left) :
      ofOver.pointsEquiv V v ∈ genericPoints (ofOver V) ↔
        v ∈ _root_.genericPoints V.left := by
    rw [genericPoints_ofOver]
    constructor
    · rintro ⟨w, hw, hwv⟩
      exact (ofOver.pointsEquiv V).injective hwv ▸ hw
    · intro hv
      exact ⟨v, hv, rfl⟩
  constructor
  · intro h
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro u hu
      apply (hV _).mp
      rw [ofOver.pointsEquiv_naturality]
      exact h.bijOn_genericPoints.mapsTo ((hU u).mpr hu)
    · intro u hu u' hu' huu'
      apply (ofOver.pointsEquiv U).injective
      apply h.bijOn_genericPoints.injOn ((hU u).mpr hu) ((hU u').mpr hu')
      rw [← ofOver.pointsEquiv_naturality, ← ofOver.pointsEquiv_naturality, huu']
    · intro v hv
      obtain ⟨x, hx, hfx⟩ := h.bijOn_genericPoints.surjOn ((hV v).mpr hv)
      obtain ⟨u, rfl⟩ := (ofOver.pointsEquiv U).surjective x
      refine ⟨u, (hU u).mp hx, ?_⟩
      apply (ofOver.pointsEquiv V).injective
      rw [ofOver.pointsEquiv_naturality]
      exact hfx
    · intro u hu
      have hs := (IsIsoStalkMapAt.spec _ _).mp (h.isIso_stalkMap ((hU u).mpr hu))
      exact hs.2.2 U V (𝟙 _) (𝟙 _) f u inferInstance inferInstance
        (by simp only [Category.comp_id, Category.id_comp]) (Points.map_id _)
  · intro h
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro x hx
      obtain ⟨u, rfl⟩ := (ofOver.pointsEquiv U).surjective x
      rw [← ofOver.pointsEquiv_naturality]
      exact (hV _).mpr (h.bijOn_genericPoints.mapsTo ((hU u).mp hx))
    · intro x hx x' hx' hxx'
      obtain ⟨u, rfl⟩ := (ofOver.pointsEquiv U).surjective x
      obtain ⟨u', rfl⟩ := (ofOver.pointsEquiv U).surjective x'
      apply congrArg (ofOver.pointsEquiv U)
      apply h.bijOn_genericPoints.injOn ((hU u).mp hx) ((hU u').mp hx')
      apply (ofOver.pointsEquiv V).injective
      simpa only [ofOver.pointsEquiv_naturality] using hxx'
    · intro y hy
      obtain ⟨v, rfl⟩ := (ofOver.pointsEquiv V).surjective y
      obtain ⟨u, hu, hfu⟩ := h.bijOn_genericPoints.surjOn ((hV v).mp hy)
      refine ⟨ofOver.pointsEquiv U u, (hU u).mpr hu, ?_⟩
      rw [← ofOver.pointsEquiv_naturality, hfu]
    · intro x hx
      obtain ⟨u, rfl⟩ := (ofOver.pointsEquiv U).surjective x
      exact ⟨U, V, 𝟙 _, 𝟙 _, f, u, inferInstance, inferInstance,
        by simp only [Category.comp_id, Category.id_comp], Points.map_id _,
        h.isIso_stalkMap ((hU u).mp hx)⟩

/-- A birational morphism of schemes over `S` induces a birational morphism of
the associated algebraic spaces. -/
instance instIsBirational_ofOverMap {S : Scheme.{u}} {U V : Over S}
    [Finite (irreducibleComponents U.left)] [Finite (irreducibleComponents V.left)]
    (f : U ⟶ V) [AlgebraicGeometry.IsBirational f.left] :
    IsBirational (ofOverMap f) :=
  (isBirational_ofOverMap_iff f).mpr inferInstance

/-- A birational morphism of decent algebraic spaces with finitely many
irreducible components restricts to a birational morphism of schemes on dense
representable open subspaces. -/
theorem exists_dense_representable_restrict {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    {f : X ⟶ Y} [IsBirational f] :
    ∃ (U V : Over S) (ιX : ofOver U ⟶ X) (ιY : ofOver V ⟶ Y) (φ : U ⟶ V),
      IsOpenImmersion ιX ∧ IsOpenImmersion ιY ∧
        (∀ (τX : TopologicalSpace (Points X)),
          IsPointsTopology X τX → @Dense (Points X) τX (Set.range (Points.map ιX))) ∧
        (∀ (τY : TopologicalSpace (Points Y)),
          IsPointsTopology Y τY → @Dense (Points Y) τY (Set.range (Points.map ιY))) ∧
        ofOverMap φ ≫ ιY = ιX ≫ f ∧ AlgebraicGeometry.IsBirational φ.left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
