/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars

/-!
# Base change of restriction of scalars

The canonical identification `Res_{Z'/B'}(X') ≅ B' ×_B Res_{Z/B}(X)` of fppf
sheaves, where `Z' = B' ×_B Z` and `X' = B' ×_B X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars

variable {S : Scheme.{u}} {X Z B B' : AlgebraicSpace S}

private theorem mapX_condition (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    pullback.fst h (f ≫ g) ≫ h = (pullback.snd h (f ≫ g) ≫ f) ≫ g :=
  by
    simpa only [Category.assoc] using (pullback.condition (f := h) (g := f ≫ g))

/-- The induced morphism `B' ×_B X ⟶ B' ×_B Z` over `B'` and `Z`. -/
def mapX (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    pullback h (f ≫ g) ⟶ pullback h g :=
  pullback.lift (pullback.fst h (f ≫ g)) (pullback.snd h (f ≫ g) ≫ f)
    (by exact mapX_condition f g h)

/-- `mapX` commutes with the projections to `B'`. -/
theorem mapX_fst (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    mapX f g h ≫ pullback.fst h g = pullback.fst h (f ≫ g) :=
  by
    unfold mapX
    exact pullback.lift_fst _ _ _

/-- `mapX` commutes with the projections to `Z` via `f`. -/
theorem mapX_snd (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    mapX f g h ≫ pullback.snd h g = pullback.snd h (f ≫ g) ≫ f :=
  by
    unfold mapX
    exact pullback.lift_snd _ _ _

/-- The induced morphism satisfies both projection identities over `B'` and `Z`. -/
theorem mapX_spec (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    mapX f g h ≫ pullback.fst h g = pullback.fst h (f ≫ g) ∧
      mapX f g h ≫ pullback.snd h g = pullback.snd h (f ≫ g) ≫ f :=
  by
    exact ⟨mapX_fst f g h, mapX_snd f g h⟩

/-- The canonical isomorphism `T ×_{B'} (B' ×_B Z) ≅ T ×_B Z` obtained by
pasting fibre-product squares. -/
def fiberIso (h : B' ⟶ B) (g : Z ⟶ B) {T : Over S} (a' : ofOver T ⟶ B') :
    fiber (pullback.fst h g) a' ≅ fiber g (a' ≫ h) :=
  fiberPullbackIso (pullback.fst h g) a' ≪≫
    pullbackRightPullbackFstIso h g a' ≪≫
    (fiberPullbackIso g (a' ≫ h)).symm

/-- `fiberIso` identifies the projections to the test scheme. -/
theorem fiberIso_fst (h : B' ⟶ B) (g : Z ⟶ B) {T : Over S} (a' : ofOver T ⟶ B') :
    (fiberIso h g a').hom ≫ fiberFst g (a' ≫ h) =
      fiberFst (pullback.fst h g) a' :=
  by
    simp [fiberIso, Category.assoc, fiberPullbackIso_inv_fst,
      fiberPullbackIso_hom_fst]

/-- `fiberIso` identifies the projections to `Z`. -/
theorem fiberIso_snd (h : B' ⟶ B) (g : Z ⟶ B) {T : Over S} (a' : ofOver T ⟶ B') :
    (fiberIso h g a').hom ≫ fiberSnd g (a' ≫ h) =
      fiberSnd (pullback.fst h g) a' ≫ pullback.snd h g :=
  by
    simp only [fiberIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      fiberPullbackIso_inv_snd, pullbackRightPullbackFstIso_hom_snd]
    rw [← Category.assoc, fiberPullbackIso_hom_snd]

private theorem fiber_condition (g : Z ⟶ B) {T : Over S} (a : ofOver T ⟶ B) :
    fiberFst g a ≫ a = fiberSnd g a ≫ g := by
  rw [← fiberPullbackIso_hom_fst g a, Category.assoc, pullback.condition,
    ← Category.assoc, fiberPullbackIso_hom_snd]

private theorem fiber_transport_snd (g : Z ⟶ B) {T : Over S}
    {a b : ofOver T ⟶ B} (hab : a = b) :
    eqToHom (congrArg (fiber g) hab) ≫ fiberSnd g b = fiberSnd g a := by
  cases hab
  simp

private theorem fiber_transport_fst (g : Z ⟶ B) {T : Over S}
    {a b : ofOver T ⟶ B} (hab : a = b) :
    eqToHom (congrArg (fiber g) hab) ≫ fiberFst g b = fiberFst g a := by
  cases hab
  simp

private theorem fiber_transport_lift (g : Z ⟶ B) {T : Over S}
    {a b : ofOver T ⟶ B} (hab : a = b) (l : fiber g b ⟶ X) :
    hab ▸ (eqToHom (congrArg (fiber g) hab) ≫ l) = l := by
  cases hab
  simp

private theorem fiber_hom_ext (g : Z ⟶ B) {T : Over S} (a : ofOver T ⟶ B)
    {W : AlgebraicSpace S} {k l : W ⟶ fiber g a}
    (hfst : k ≫ fiberFst g a = l ≫ fiberFst g a)
    (hsnd : k ≫ fiberSnd g a = l ≫ fiberSnd g a) : k = l := by
  apply (cancel_mono (fiberPullbackIso g a).hom).1
  apply pullback.hom_ext
  · simpa only [Category.assoc, fiberPullbackIso_hom_fst] using hfst
  · simpa only [Category.assoc, fiberPullbackIso_hom_snd] using hsnd

private theorem fiberIso_hom_naturality (h : B' ⟶ B) (g : Z ⟶ B)
    {T T' : Over S} (φ : T' ⟶ T) (a : ofOver T ⟶ B') :
    fiberMap (T := T) (T' := T') (pullback.fst h g) φ a ≫ (fiberIso h g (T := T) a).hom =
      (fiberIso h g (T := T') ((yoneda.map φ : ofOver T' ⟶ ofOver T) ≫ a)).hom ≫
        eqToHom (congrArg (fiber g (T := T'))
          (Category.assoc (yoneda.map φ : ofOver T' ⟶ ofOver T) a h)) ≫
        fiberMap (T := T) (T' := T') g φ (a ≫ h) := by
  apply fiber_hom_ext g (T := T) (a ≫ h)
  · calc
      (fiberMap (T := T) (T' := T') (pullback.fst h g) φ a ≫ (fiberIso h g (T := T) a).hom) ≫ fiberFst g (a ≫ h) =
          fiberMap (T := T) (T' := T') (pullback.fst h g) φ a ≫ fiberFst (pullback.fst h g) a := by
        rw [Category.assoc, fiberIso_fst]
      _ = fiberFst (pullback.fst h g) ((yoneda.map φ : ofOver T' ⟶ ofOver T) ≫ a) ≫
          yoneda.map φ := fiberMap_fst _ _ _
      _ = _ := by
        simp only [Category.assoc]
        rw [fiberMap_fst, ← Category.assoc (eqToHom _)]
        erw [fiber_transport_fst g (T := T')
          (Category.assoc (yoneda.map φ : ofOver T' ⟶ ofOver T) a h)]
        rw [← Category.assoc]
        erw [fiberIso_fst h g (T := T') ((yoneda.map φ : ofOver T' ⟶ ofOver T) ≫ a)]
  · calc
      (fiberMap (T := T) (T' := T') (pullback.fst h g) φ a ≫ (fiberIso h g (T := T) a).hom) ≫ fiberSnd g (a ≫ h) =
          fiberMap (T := T) (T' := T') (pullback.fst h g) φ a ≫ fiberSnd (pullback.fst h g) a ≫
            pullback.snd h g := by
        rw [Category.assoc, fiberIso_snd]
      _ = fiberSnd (pullback.fst h g) ((yoneda.map φ : ofOver T' ⟶ ofOver T) ≫ a) ≫
          pullback.snd h g := by
        rw [← Category.assoc, fiberMap_snd]
      _ = _ := by
        simp only [Category.assoc]
        rw [fiberMap_snd]
        erw [fiber_transport_snd g (T := T')
          (Category.assoc (yoneda.map φ : ofOver T' ⟶ ofOver T) a h)]
        erw [fiberIso_snd h g (T := T') ((yoneda.map φ : ofOver T' ⟶ ofOver T) ≫ a)]

private theorem inv_naturality {W W' V V' : AlgebraicSpace S}
    (i : W ≅ W') (j : V ≅ V') {a : W ⟶ V} {b : W' ⟶ V'}
    (ha : a ≫ j.hom = i.hom ≫ b) : i.inv ≫ a = b ≫ j.inv := by
  apply (cancel_epi i.hom).1
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← ha, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem pair_ext {f : X ⟶ Z} {g : Z ⟶ B} {T : Over S}
    {p q : Pair f g T} (hbase : p.base = q.base)
    (hlift : Eq.ndrec (motive := fun a : ofOver T ⟶ B => fiber g a ⟶ X)
      p.lift hbase = q.lift) : p = q := by
  rcases p with ⟨a, b, hb⟩
  rcases q with ⟨a', b', hb'⟩
  cases hbase
  cases hlift
  rfl

private theorem pairMap_overZ (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) {T : Over S}
    (p : Pair (mapX f g h) (pullback.fst h g) T) :
    ((fiberIso h g p.base).inv ≫ p.lift ≫ pullback.snd h (f ≫ g)) ≫ f =
      fiberSnd g (p.base ≫ h) :=
  by
    apply (cancel_epi (fiberIso h g p.base).hom).1
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← mapX_snd, ← Category.assoc]
    erw [p.overZ]
    exact (fiberIso_snd h g p.base).symm

/-- The forward transformation sends a pair over `B'` to the pair over `B`
with base `a' ≫ h` and lift transported along `fiberIso`. -/
def pairMap (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) {T : Over S}
    (p : Pair (mapX f g h) (pullback.fst h g) T) : Pair f g T :=
  Pair.of (p.base ≫ h)
    ((fiberIso h g p.base).inv ≫ p.lift ≫ pullback.snd h (f ≫ g))
    (by exact pairMap_overZ f g h p)

private theorem pairMap_base (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) {T : Over S}
    (p : Pair (mapX f g h) (pullback.fst h g) T) :
    (pairMap f g h p).base = p.base ≫ h := rfl

private theorem pairMap_lift (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) {T : Over S}
    (p : Pair (mapX f g h) (pullback.fst h g) T) :
    (pairMap f g h p).lift =
      (fiberIso h g p.base).inv ≫ p.lift ≫ pullback.snd h (f ≫ g) := rfl

private theorem pairInv_condition (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B)
    {T : Over S} (a' : ofOver T ⟶ B') (q : Pair f g T) (hq : a' ≫ h = q.base) :
    (fiberFst (pullback.fst h g) a' ≫ a') ≫ h =
      ((fiberIso h g a').hom ≫ (eqToHom (congrArg (fiber g) hq) ≫ q.lift)) ≫
        (f ≫ g) :=
  by
    calc
      (fiberFst (pullback.fst h g) a' ≫ a') ≫ h =
          (fiberIso h g a').hom ≫ (fiberFst g (a' ≫ h) ≫ (a' ≫ h)) := by
        rw [← Category.assoc (fiberIso h g a').hom, fiberIso_fst]
        simp only [Category.assoc]
      _ = (fiberIso h g a').hom ≫ (fiberSnd g (a' ≫ h) ≫ g) := by
        rw [fiber_condition]
      _ = ((fiberIso h g a').hom ≫ (eqToHom (congrArg (fiber g) hq) ≫ q.lift)) ≫
          (f ≫ g) := by
        simp only [Category.assoc]
        erw [reassoc_of% q.overZ, ← Category.assoc (eqToHom _), fiber_transport_snd g hq]

private def pairInvLift (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) {T : Over S}
    (a' : ofOver T ⟶ B') (q : Pair f g T) (hq : a' ≫ h = q.base) :
    fiber (pullback.fst h g) a' ⟶ pullback h (f ≫ g) :=
  pullback.lift (fiberFst (pullback.fst h g) a' ≫ a')
    ((fiberIso h g a').hom ≫ (eqToHom (congrArg (fiber g) hq) ≫ q.lift))
    (pairInv_condition f g h a' q hq)

private theorem pairInv_overZ (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) {T : Over S}
    (a' : ofOver T ⟶ B') (q : Pair f g T) (hq : a' ≫ h = q.base) :
    pairInvLift f g h a' q hq ≫ mapX f g h = fiberSnd (pullback.fst h g) a' :=
  by
    apply pullback.hom_ext
    · show (pairInvLift f g h a' q hq ≫ mapX f g h) ≫ pullback.fst h g =
        fiberSnd (pullback.fst h g) a' ≫ pullback.fst h g
      rw [Category.assoc, mapX_fst, pairInvLift, pullback.lift_fst]
      exact fiber_condition (pullback.fst h g) a'
    · show (pairInvLift f g h a' q hq ≫ mapX f g h) ≫ pullback.snd h g =
        fiberSnd (pullback.fst h g) a' ≫ pullback.snd h g
      rw [Category.assoc, mapX_snd, ← Category.assoc, pairInvLift, pullback.lift_snd]
      simp only [Category.assoc]
      erw [q.overZ, fiber_transport_snd g hq, fiberIso_snd]

/-- The inverse transformation reconstructs a pair over `B'` from a `B'`-point
and a compatible restriction-of-scalars pair over `B`. -/
def pairInv (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) {T : Over S}
    (a' : ofOver T ⟶ B') (q : Pair f g T) (hq : a' ≫ h = q.base) :
    Pair (mapX f g h) (pullback.fst h g) T :=
  Pair.of a'
    (pullback.lift (fiberFst (pullback.fst h g) a' ≫ a')
      ((fiberIso h g a').hom ≫ (eqToHom (congrArg (fiber g) hq) ≫ q.lift))
      (by exact pairInv_condition f g h a' q hq))
    (by exact pairInv_overZ f g h a' q hq)

private theorem pairInv_lift (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) {T : Over S}
    (a' : ofOver T ⟶ B') (q : Pair f g T) (hq : a' ≫ h = q.base) :
    (pairInv f g h a' q hq).lift = pairInvLift f g h a' q hq := rfl

private theorem pairEquiv_left_inv (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B)
    (T : Over S) :
    Function.LeftInverse
      (fun (p : { p : (ofOver T ⟶ B') × Pair f g T // p.1 ≫ h = p.2.base }) ↦
        pairInv f g h p.1.1 p.1.2 p.2)
      (fun (p : Pair (mapX f g h) (pullback.fst h g) T) ↦
        (⟨⟨p.base, pairMap f g h p⟩, rfl⟩ :
          { p : (ofOver T ⟶ B') × Pair f g T // p.1 ≫ h = p.2.base })) :=
  by
    intro p
    refine pair_ext (p := pairInv f g h p.base (pairMap f g h p) rfl) (q := p) rfl ?_
    change (pairInv f g h p.base (pairMap f g h p) rfl).lift = p.lift
    rw [pairInv_lift]
    apply pullback.hom_ext
    · show _ ≫ pullback.fst h (f ≫ g) = p.lift ≫ pullback.fst h (f ≫ g)
      rw [pairInvLift]
      erw [pullback.lift_fst]
      rw [← mapX_fst f g h, ← Category.assoc]
      erw [p.overZ]
      exact fiber_condition (pullback.fst h g) p.base
    · show _ ≫ pullback.snd h (f ≫ g) = p.lift ≫ pullback.snd h (f ≫ g)
      rw [pairInvLift]
      erw [pullback.lift_snd]
      change (fiberIso h g p.base).hom ≫ (fiberIso h g p.base).inv ≫
        (p.lift ≫ pullback.snd h (f ≫ g)) = p.lift ≫ pullback.snd h (f ≫ g)
      exact Iso.hom_inv_id_assoc _ _

private theorem pairEquiv_right_inv (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B)
    (T : Over S) :
    Function.RightInverse
      (fun (p : { p : (ofOver T ⟶ B') × Pair f g T // p.1 ≫ h = p.2.base }) ↦
        pairInv f g h p.1.1 p.1.2 p.2)
      (fun (p : Pair (mapX f g h) (pullback.fst h g) T) ↦
        (⟨⟨p.base, pairMap f g h p⟩, rfl⟩ :
          { p : (ofOver T ⟶ B') × Pair f g T // p.1 ≫ h = p.2.base })) :=
  by
    rintro ⟨⟨a', q⟩, hq⟩
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · refine pair_ext (p := pairMap f g h (pairInv f g h a' q hq)) (q := q) hq ?_
      have hlift : (pairMap f g h (pairInv f g h a' q hq)).lift =
          eqToHom (congrArg (fiber g) hq) ≫ q.lift := by
        change (fiberIso h g a').inv ≫ (pairInv f g h a' q hq).lift ≫
          pullback.snd h (f ≫ g) = _
        rw [pairInv_lift]
        simp [pairInvLift, pullback.lift_snd]
      rw [hlift]
      exact fiber_transport_lift g hq q.lift

/-- Pairs over the base change correspond to compatible pairs of a `B'`-point
and a restriction-of-scalars point over `B`. -/
def pairEquiv (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) (T : Over S) :
    Pair (mapX f g h) (pullback.fst h g) T ≃
      { p : (ofOver T ⟶ B') × Pair f g T // p.1 ≫ h = p.2.base } where
  toFun p := ⟨⟨p.base, pairMap f g h p⟩, rfl⟩
  invFun p := pairInv f g h p.1.1 p.1.2 p.2
  left_inv := by exact pairEquiv_left_inv f g h T
  right_inv := by exact pairEquiv_right_inv f g h T

/-- `pairEquiv` sends a pair to its `B'`-point together with `pairMap`. -/
theorem pairEquiv_apply (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) {T : Over S}
    (p : Pair (mapX f g h) (pullback.fst h g) T) :
    (pairEquiv f g h T p).1 = ⟨p.base, pairMap f g h p⟩ :=
  rfl

/-- The inverse of `pairEquiv` is `pairInv` on a compatible pair of points. -/
theorem pairEquiv_symm_apply (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) {T : Over S}
    (p : (ofOver T ⟶ B') × Pair f g T) (hp : p.1 ≫ h = p.2.base) :
    (pairEquiv f g h T).symm ⟨p, hp⟩ = pairInv f g h p.1 p.2 hp :=
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem toRestrictionOfScalars_naturality
    (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T') :
    (restrictionOfScalars (mapX f g h) (pullback.fst h g)).map φ ≫
        TypeCat.ofHom (pairMap f g h (T := T'.unop)) =
      TypeCat.ofHom (pairMap f g h (T := T.unop)) ≫
        (restrictionOfScalars f g).map φ :=
  by
    ext p
    change Pair (mapX f g h) (pullback.fst h g) T.unop at p
    change pairMap f g h (Pair.precomp φ.unop p) =
      Pair.precomp φ.unop (pairMap f g h p)
    refine pair_ext (p := pairMap f g h (Pair.precomp φ.unop p))
      (q := Pair.precomp φ.unop (pairMap f g h p))
      (Category.assoc (yoneda.map φ.unop : ofOver T'.unop ⟶ ofOver T.unop) p.base h) ?_
    have hf := fiberIso_hom_naturality h g (T := T.unop) (T' := T'.unop) φ.unop p.base
    let i := fiberIso h g (T := T'.unop)
      ((yoneda.map φ.unop : ofOver T'.unop ⟶ ofOver T.unop) ≫ p.base)
    let j := fiberIso h g (T := T.unop) p.base
    have hn := inv_naturality
      i j hf
    have hlift := congrArg (fun k => k ≫ p.lift ≫ pullback.snd h (f ≫ g)) hn
    simp only [Category.assoc] at hlift
    simp only [pairMap_base, pairMap_lift, Pair.precomp_lift, Category.assoc]
    erw [hlift]
    exact fiber_transport_lift g (T := T'.unop)
      (Category.assoc (yoneda.map φ.unop : ofOver T'.unop ⟶ ofOver T.unop) p.base h) _

/-- The sheaf morphism `Res_{Z'/B'}(X') ⟶ Res_{Z/B}(X)` induced by `pairMap`. -/
def toRestrictionOfScalars (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    sheaf (mapX f g h) (pullback.fst h g) ⟶ sheaf f g :=
  Sheaf.homEquiv.symm
    { app T := TypeCat.ofHom (pairMap f g h)
      naturality := by exact fun _ _ φ ↦ toRestrictionOfScalars_naturality f g h φ }

/-- Components of `toRestrictionOfScalars` are `pairMap`. -/
theorem toRestrictionOfScalars_app (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B)
    (T : (Over S)ᵒᵖ) (p : Pair (mapX f g h) (pullback.fst h g) T.unop) :
    (toRestrictionOfScalars f g h).hom.app T p = pairMap f g h p :=
  rfl

private theorem baseChangeInv_compatibility (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B)
    (T : (Over S)ᵒᵖ) (x : (pullback (toSheaf.map h) (toBase f g)).obj.obj T) :
    yonedaEquiv.symm
        ((pullback.fst (toSheaf.map h) (toBase f g)).hom.app T x).down ≫ h =
      ((pullback.snd (toSheaf.map h) (toBase f g)).hom.app T x).base := by
    have hc := (pullback.condition (f := toSheaf.map h) (g := toBase f g))
    have hcx := congrArg (fun k => (k.hom.app T x).down) hc
    change h.app T ((pullback.fst (toSheaf.map h) (toBase f g)).hom.app T x).down =
      yonedaEquiv ((pullback.snd (toSheaf.map h) (toBase f g)).hom.app T x).base at hcx
    apply yonedaEquiv.injective
    simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using hcx

private def baseChangeInvApp (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B)
    (T : (Over S)ᵒᵖ) :
    (pullback (toSheaf.map h) (toBase f g)).obj.obj T →
      Pair (mapX f g h) (pullback.fst h g) T.unop :=
  fun x ↦ pairInv f g h
    (yonedaEquiv.symm
      ((pullback.fst (toSheaf.map h) (toBase f g)).hom.app T x).down)
    ((pullback.snd (toSheaf.map h) (toBase f g)).hom.app T x)
    (baseChangeInv_compatibility f g h T x)

private theorem baseChangeInvApp_pairMap (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B)
    (T : (Over S)ᵒᵖ) (x : (pullback (toSheaf.map h) (toBase f g)).obj.obj T) :
    pairMap f g h (baseChangeInvApp f g h T x) =
      (pullback.snd (toSheaf.map h) (toBase f g)).hom.app T x := by
  exact congrArg (fun p => p.val.2)
    ((pairEquiv f g h T.unop).apply_symm_apply
      ⟨(yonedaEquiv.symm
          ((pullback.fst (toSheaf.map h) (toBase f g)).hom.app T x).down,
        (pullback.snd (toSheaf.map h) (toBase f g)).hom.app T x),
        baseChangeInv_compatibility f g h T x⟩)

private theorem baseChangeInv_naturality (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B)
    {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T') :
    (pullback (toSheaf.map h) (toBase f g)).obj.map φ ≫
        TypeCat.ofHom (baseChangeInvApp f g h T') =
      TypeCat.ofHom (baseChangeInvApp f g h T) ≫
        (restrictionOfScalars (mapX f g h) (pullback.fst h g)).map φ :=
  by
    ext x
    change baseChangeInvApp f g h T'
        ((pullback (toSheaf.map h) (toBase f g)).obj.map φ x) =
      (restrictionOfScalars (mapX f g h) (pullback.fst h g)).map φ
        (baseChangeInvApp f g h T x)
    apply (pairEquiv f g h T'.unop).injective
    apply Subtype.ext
    apply Prod.ext
    · change yonedaEquiv.symm
        ((pullback.fst (toSheaf.map h) (toBase f g)).hom.app T'
          ((pullback (toSheaf.map h) (toBase f g)).obj.map φ x)).down =
        (yoneda.map φ.unop : ofOver T'.unop ⟶ ofOver T.unop) ≫
          yonedaEquiv.symm ((pullback.fst (toSheaf.map h) (toBase f g)).hom.app T x).down
      rw [yonedaEquiv_symm_naturality_left]
      congr 1
      exact congrArg ULift.down
        ((pullback.fst (toSheaf.map h) (toBase f g)).hom.naturality_apply φ x)
    · change pairMap f g h
        (baseChangeInvApp f g h T'
          ((pullback (toSheaf.map h) (toBase f g)).obj.map φ x)) =
        pairMap f g h ((restrictionOfScalars (mapX f g h) (pullback.fst h g)).map φ
          (baseChangeInvApp f g h T x))
      rw [baseChangeInvApp_pairMap]
      have hs := (pullback.snd (toSheaf.map h) (toBase f g)).hom.naturality_apply φ x
      have hn := congrArg (fun k => k (baseChangeInvApp f g h T x))
        (toRestrictionOfScalars_naturality f g h φ)
      have hq := baseChangeInvApp_pairMap f g h T x
      exact hs.trans ((congrArg ((restrictionOfScalars f g).map φ) hq).symm.trans hn.symm)


private def baseChangeInv (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    pullback (toSheaf.map h) (toBase f g) ⟶
      sheaf (mapX f g h) (pullback.fst h g) :=
  Sheaf.homEquiv.symm
    { app T := TypeCat.ofHom (baseChangeInvApp f g h T)
      naturality := fun _ _ φ ↦ baseChangeInv_naturality f g h φ }

private theorem baseChangeHom_condition (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    toBase (mapX f g h) (pullback.fst h g) ≫ toSheaf.map h =
      toRestrictionOfScalars f g h ≫ toBase f g :=
  by
    apply Sheaf.hom_ext
    ext T p
    change ULift.up (h.app T (yonedaEquiv p.base)) =
      ULift.up (yonedaEquiv (p.base ≫ h))
    rfl

private def baseChangeHom (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    sheaf (mapX f g h) (pullback.fst h g) ⟶
      pullback (toSheaf.map h) (toBase f g) :=
  pullback.lift (toBase (mapX f g h) (pullback.fst h g))
    (toRestrictionOfScalars f g h) (baseChangeHom_condition f g h)

private theorem baseChange_hom_inv_id (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    baseChangeHom f g h ≫ baseChangeInv f g h =
      𝟙 (sheaf (mapX f g h) (pullback.fst h g)) :=
  by
    apply Sheaf.hom_ext
    ext T p
    have hf : (pullback.fst (toSheaf.map h) (toBase f g)).hom.app T
        ((baseChangeHom f g h).hom.app T p) = ULift.up (yonedaEquiv p.base) :=
      congrArg (fun k => k.hom.app T p)
        (show baseChangeHom f g h ≫ pullback.fst (toSheaf.map h) (toBase f g) =
          toBase (mapX f g h) (pullback.fst h g) from pullback.lift_fst _ _ _)
    have hs : (pullback.snd (toSheaf.map h) (toBase f g)).hom.app T
        ((baseChangeHom f g h).hom.app T p) = pairMap f g h p :=
      congrArg (fun k => k.hom.app T p)
        (show baseChangeHom f g h ≫ pullback.snd (toSheaf.map h) (toBase f g) =
          toRestrictionOfScalars f g h from pullback.lift_snd _ _ _)
    change baseChangeInvApp f g h T ((baseChangeHom f g h).hom.app T p) = p
    simpa only [baseChangeInvApp, hf, hs, ULift.down_up, Equiv.symm_apply_apply] using
      (pairEquiv_left_inv f g h T.unop p)

private theorem baseChange_inv_hom_id (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    baseChangeInv f g h ≫ baseChangeHom f g h =
      𝟙 (pullback (toSheaf.map h) (toBase f g)) :=
  by
    apply pullback.hom_ext
    · show (baseChangeInv f g h ≫ baseChangeHom f g h) ≫
        pullback.fst (toSheaf.map h) (toBase f g) =
          𝟙 _ ≫ pullback.fst (toSheaf.map h) (toBase f g)
      rw [Category.assoc, baseChangeHom, pullback.lift_fst, Category.id_comp]
      apply Sheaf.hom_ext
      ext T x
      change ULift.up (yonedaEquiv (yonedaEquiv.symm
        ((pullback.fst (toSheaf.map h) (toBase f g)).hom.app T x).down)) =
          (pullback.fst (toSheaf.map h) (toBase f g)).hom.app T x
      apply ULift.ext
      simp
    · show (baseChangeInv f g h ≫ baseChangeHom f g h) ≫
        pullback.snd (toSheaf.map h) (toBase f g) =
          𝟙 _ ≫ pullback.snd (toSheaf.map h) (toBase f g)
      rw [Category.assoc, baseChangeHom, pullback.lift_snd, Category.id_comp]
      apply Sheaf.hom_ext
      ext T x
      exact baseChangeInvApp_pairMap f g h T x

/-- Restriction of scalars commutes canonically with arbitrary base change
as fppf sheaves on schemes over `S`. -/
def pullbackIso (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    sheaf (mapX f g h) (pullback.fst h g) ≅
      pullback (toSheaf.map h) (toBase f g) where
  hom := private baseChangeHom f g h
  inv := private baseChangeInv f g h
  hom_inv_id := by exact baseChange_hom_inv_id f g h
  inv_hom_id := by exact baseChange_inv_hom_id f g h

/-- The first projection of `pullbackIso.hom` is the structure morphism
of the base-changed restriction of scalars. -/
theorem pullbackIso_hom_fst (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    (pullbackIso f g h).hom ≫ pullback.fst (toSheaf.map h) (toBase f g) =
      toBase (mapX f g h) (pullback.fst h g) :=
  by
    exact pullback.lift_fst _ _ _

/-- The second projection of `pullbackIso.hom` is `toRestrictionOfScalars`. -/
theorem pullbackIso_hom_snd (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    (pullbackIso f g h).hom ≫ pullback.snd (toSheaf.map h) (toBase f g) =
      toRestrictionOfScalars f g h :=
  by
    exact pullback.lift_snd _ _ _

/-- The square of restriction-of-scalars sheaves induced by `B' ⟶ B`
is cartesian in fppf sheaves on schemes over `S`. -/
theorem baseChange_isPullback (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    IsPullback (toBase (mapX f g h) (pullback.fst h g))
      (toRestrictionOfScalars f g h) (toSheaf.map h) (toBase f g) :=
  by
    exact IsPullback.of_iso_pullback ⟨baseChangeHom_condition f g h⟩
      (pullbackIso f g h) (pullbackIso_hom_fst f g h) (pullbackIso_hom_snd f g h)

end AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars
