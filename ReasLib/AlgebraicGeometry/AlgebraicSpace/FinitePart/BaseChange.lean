/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Sheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Iso
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Base change of finite-part sheaves -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The identification `T ×_{Y'} X' ≅ T ×_Y X` induced by a fibre product square of
algebraic spaces over `S`. -/
def fiberIso {S : Scheme.{u}} {X X' Y Y' T : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) (a' : T ⟶ Y') :
    pullback a' fX' ≅ pullback (a' ≫ pY) fX :=
  ((IsPullback.of_hasPullback a' fX').flip.paste_horiz h).flip.isoPullback

/-- The first projection of `fiberIso h a'` recovers `pullback.fst a' fX'`. -/
theorem fiberIso_hom_fst {S : Scheme.{u}} {X X' Y Y' T : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) (a' : T ⟶ Y') :
    (fiberIso h a').hom ≫ pullback.fst (a' ≫ pY) fX = pullback.fst a' fX' :=
  IsPullback.isoPullback_hom_fst _

/-- The second projection of `fiberIso h a'` recovers `pullback.snd a' fX' ≫ pX`. -/
theorem fiberIso_hom_snd {S : Scheme.{u}} {X X' Y Y' T : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) (a' : T ⟶ Y') :
    (fiberIso h a').hom ≫ pullback.snd (a' ≫ pY) fX = pullback.snd a' fX' ≫ pX :=
  IsPullback.isoPullback_hom_snd _

namespace FinitePart.Point

/-- The open reconstructed from the transported points-open is finite over the test scheme. -/
theorem congrIso_isFinite {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) {T : Over S} (p : Point fX' T) :
    IsFinite
      ((OpenSubspace.fromOpens
        (OpenSubspace.mapIso (fiberIso h p.a) p.subspace).pointsOpens).ι ≫
          pullback.fst (p.a ≫ pY) fX) := by
  apply FinitePart.SubspacePoint.toPoint_isFinite
    (FinitePart.SubspacePoint.of (p.a ≫ pY)
      (OpenSubspace.mapIso (fiberIso h p.a) p.subspace) ?_)
  change IsFinite ((p.subspace.ι ≫ (fiberIso h p.a).hom) ≫
    pullback.fst (p.a ≫ pY) fX)
  rw [Category.assoc, fiberIso_hom_fst]
  exact p.isFinite

/-- Transport a finite-part pair along a fibre product square of algebraic spaces,
sending `(a', Z')` to `(a' ≫ pY, Z)` with `Z` the open subspace of `T ×_Y X`
transported along `fiberIso`. -/
def congrIso {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) {T : Over S} (p : Point fX' T) :
    Point fX T where
  a := p.a ≫ pY
  Z := (OpenSubspace.mapIso (fiberIso h p.a) p.subspace).pointsOpens
  isFinite := congrIso_isFinite h p

/-- `congrIso` postcomposes the morphism to the base with `pY`. -/
theorem congrIso_a {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) {T : Over S} (p : Point fX' T) :
    (congrIso h p).a = p.a ≫ pY :=
  rfl

end FinitePart.Point

private theorem mapIso_pointsOpens {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (e : X ≅ Y) (U : OpenSubspace X) :
    (OpenSubspace.mapIso e U).pointsOpens =
      TopologicalSpace.Opens.comap
        ⟨Points.map e.inv, Points.continuous_map e.inv⟩ U.pointsOpens := by
  apply SetLike.coe_injective
  change Set.range (Points.map (U.ι ≫ e.hom)) =
    Points.map e.inv ⁻¹' Set.range (Points.map U.ι)
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    rw [Points.map_comp, ← Points.map_comp, e.hom_inv_id, Points.map_id]
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [Points.map_comp, hz, ← Points.map_comp, e.inv_hom_id, Points.map_id]

set_option backward.isDefEq.respectTransparency false in
/-- Transport of finite-part pairs along a pullback square commutes with restriction. -/
theorem finitePartMap_naturality {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) {T T' : (Over S)ᵒᵖ} (g : T ⟶ T') :
    (finitePartSheaf fX').obj.map g ≫
        TypeCat.ofHom (fun (p : FinitePart.Point fX' T'.unop) ↦
          FinitePart.Point.congrIso h p) =
      TypeCat.ofHom (fun (p : FinitePart.Point fX' T.unop) ↦
        FinitePart.Point.congrIso h p) ≫ (finitePartSheaf fX).obj.map g := by
  apply ConcreteCategory.hom_ext
  intro p
  change FinitePart.Point fX' T.unop at p
  change FinitePart.Point.congrIso h (p.restrict g.unop) =
    (FinitePart.Point.congrIso h p).restrict g.unop
  have he : FinitePart.baseChange g.unop fX' p.a ≫ (fiberIso h p.a).hom =
      (fiberIso h (ofOverMap g.unop ≫ p.a)).hom ≫
        FinitePart.baseChange g.unop fX (p.a ≫ pY) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, fiberIso_hom_fst, FinitePart.baseChange_fst]
      rw [← Category.assoc]
      exact (congrArg (fun k ↦ k ≫ ofOverMap g.unop)
        (fiberIso_hom_fst h (ofOverMap g.unop ≫ p.a))).symm
    · simp only [Category.assoc, fiberIso_hom_snd, FinitePart.baseChange_snd]
      rw [← Category.assoc, FinitePart.baseChange_snd]
      exact (fiberIso_hom_snd h (ofOverMap g.unop ≫ p.a)).symm
  have hi : (fiberIso h (ofOverMap g.unop ≫ p.a)).inv ≫
      FinitePart.baseChange g.unop fX' p.a =
      FinitePart.baseChange g.unop fX (p.a ≫ pY) ≫ (fiberIso h p.a).inv := by
    apply (cancel_mono (fiberIso h p.a).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [he, Iso.inv_hom_id_assoc]
  dsimp only [FinitePart.Point.congrIso, FinitePart.Point.restrict]
  congr 1
  simp only [mapIso_pointsOpens, FinitePart.Point.subspace_pointsOpens]
  apply SetLike.coe_injective
  ext x
  change (Points.map (FinitePart.baseChange g.unop fX' p.a)
      (Points.map (fiberIso h (ofOverMap g.unop ≫ p.a)).inv x) ∈ p.Z) ↔
    (Points.map (fiberIso h p.a).inv
      (Points.map (FinitePart.baseChange g.unop fX (p.a ≫ pY)) x) ∈ p.Z)
  rw [← Points.map_comp, ← Points.map_comp, hi]

/-- The comparison of finite-part sheaves induced by a fibre product square of
algebraic spaces over `S`. -/
def finitePartMap {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) :
    finitePartSheaf fX' ⟶ finitePartSheaf fX :=
  ObjectProperty.homMk
    { app T := TypeCat.ofHom fun (p : FinitePart.Point fX' T.unop) ↦
        FinitePart.Point.congrIso h p
      naturality := fun _ _ g ↦ finitePartMap_naturality h g }

/-- Components of `finitePartMap h` are `FinitePart.Point.congrIso h`. -/
theorem finitePartMap_app {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) (T : (Over S)ᵒᵖ) :
    (finitePartMap h).hom.app T =
      TypeCat.ofHom fun (p : FinitePart.Point fX' T.unop) ↦ FinitePart.Point.congrIso h p :=
  rfl

/-- On a pair `(a', Z')` over `T`, `finitePartMap h` postcomposes `a'` with `pY`. -/
theorem finitePartMap_a {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) {T : Over S} (p : FinitePart.Point fX' T) :
    ((finitePartMap h).hom.app (op T) p).a = p.a ≫ pY :=
  rfl

/-- On a pair `(a', Z')` over `T`, `finitePartMap h` is `FinitePart.Point.congrIso h`. -/
theorem finitePartMap_spec {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) {T : Over S} (p : FinitePart.Point fX' T) :
    (finitePartMap h).hom.app (op T) p = FinitePart.Point.congrIso h p :=
  rfl

/-- The comparison `finitePartMap h` commutes with the structure morphisms to `Y'` and
`Y`. -/
theorem finitePartMap_comm {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) :
    finitePartMap h ≫ finitePartTo fX = finitePartTo fX' ≫ (toFppfSheaf S).map pY := by
  apply ObjectProperty.hom_ext
  ext T p
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- On a scheme `T` over `S`, the finite-part sheaf square is a fibre product of
types. -/
theorem finitePart_isPullback_app {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) (T : (Over S)ᵒᵖ) :
    IsPullback ((finitePartMap h).hom.app T) ((finitePartTo fX').hom.app T)
      ((finitePartTo fX).hom.app T) (((toFppfSheaf S).map pY).hom.app T) := by
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · exact congrArg (fun k ↦ k.hom.app T) (finitePartMap_comm h)
  · intro p q hpq
    change FinitePart.Point fX' T.unop at p q
    change (FinitePart.Point.congrIso h p = FinitePart.Point.congrIso h q) ∧
      (ULift.up p.a_elem = ULift.up q.a_elem) at hpq
    have ha : p.a = q.a := yonedaEquiv.injective (congrArg ULift.down hpq.2)
    rcases p with ⟨a, Z, hf⟩
    rcases q with ⟨b, W, hg⟩
    dsimp only at ha
    cases ha
    have hZ := eq_of_heq (FinitePart.Point.mk.inj hpq.1).2
    simp only [mapIso_pointsOpens, FinitePart.Point.subspace_pointsOpens] at hZ
    have hZW : Z = W := by
      apply SetLike.ext
      intro z
      have hz := SetLike.ext_iff.mp hZ (Points.map (fiberIso h a).hom z)
      change (Points.map (fiberIso h a).inv (Points.map (fiberIso h a).hom z) ∈ Z) ↔
        (Points.map (fiberIso h a).inv (Points.map (fiberIso h a).hom z) ∈ W) at hz
      simpa only [← Points.map_comp, Iso.hom_inv_id, Points.map_id] using hz
    cases hZW
    rfl
  · intro p b hab
    change FinitePart.Point fX T.unop at p
    change ULift.up p.a_elem = ULift.up (pY.app T b.down) at hab
    let a' : ofOver T.unop ⟶ Y' := yonedaEquiv.symm b.down
    have ha : p.a = a' ≫ pY := by
      apply yonedaEquiv.injective
      change p.a_elem = yonedaEquiv (a' ≫ pY)
      rw [yonedaEquiv_comp]
      change p.a_elem = pY.app T (yonedaEquiv a')
      simpa only [a', Equiv.apply_symm_apply] using congrArg ULift.down hab
    rcases p with ⟨a, Z, hf⟩
    dsimp only at ha
    cases ha
    let W := OpenSubspace.mapIso (fiberIso h a').symm (OpenSubspace.fromOpens Z)
    have hW : IsFinite (W.ι ≫ pullback.fst a' fX') := by
      change IsFinite (((OpenSubspace.fromOpens Z).ι ≫ (fiberIso h a').inv) ≫
        pullback.fst a' fX')
      have hfst : (fiberIso h a').inv ≫ pullback.fst a' fX' =
          pullback.fst (a' ≫ pY) fX := by
        apply (cancel_epi (fiberIso h a').hom).mp
        rw [Iso.hom_inv_id_assoc]
        exact (fiberIso_hom_fst h a').symm
      rw [Category.assoc, hfst]
      exact hf
    letI : IsFinite (W.ι ≫ pullback.fst a' fX') := hW
    let q : FinitePart.Point fX' T.unop := FinitePart.Point.ofSubspace a' W
    refine ⟨q, ?_, ?_⟩
    · change FinitePart.Point.congrIso h q = _
      dsimp only [q, FinitePart.Point.ofSubspace, FinitePart.SubspacePoint.toPoint,
        FinitePart.SubspacePoint.of, FinitePart.Point.of, FinitePart.Point.congrIso]
      congr 1
      simp only [mapIso_pointsOpens, FinitePart.Point.subspace_pointsOpens]
      change TopologicalSpace.Opens.comap
        ⟨Points.map (fiberIso h a').inv, Points.continuous_map _⟩ W.pointsOpens = Z
      rw [mapIso_pointsOpens]
      apply SetLike.coe_injective
      ext x
      change (Points.map (fiberIso h a').hom
        (Points.map (fiberIso h a').inv x) ∈ (OpenSubspace.fromOpens Z).pointsSet) ↔ x ∈ Z
      rw [← Points.map_comp, Iso.inv_hom_id, Points.map_id,
        OpenSubspace.fromOpens_pointsSet]
      rfl
    · change ULift.up (yonedaEquiv a') = b
      exact ULift.ext _ _ (Equiv.apply_symm_apply _ _)

/-- Finite-part sheaves commute with arbitrary base change of algebraic spaces. -/
theorem finitePart_isPullback {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) :
    IsPullback (finitePartMap h) (finitePartTo fX') (finitePartTo fX)
      ((toFppfSheaf S).map pY) := by
  apply IsPullback.of_map_of_faithful (sheafToPresheaf _ _)
  exact IsPullback.of_forall_isPullback_app (finitePart_isPullback_app h)

end AlgebraicGeometry.AlgebraicSpace
