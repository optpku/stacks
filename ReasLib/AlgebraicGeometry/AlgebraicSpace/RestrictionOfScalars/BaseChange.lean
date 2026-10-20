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
  sorry

/-- The induced morphism `B' ×_B X ⟶ B' ×_B Z` over `B'` and `Z`. -/
def mapX (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    pullback h (f ≫ g) ⟶ pullback h g :=
  pullback.lift (pullback.fst h (f ≫ g)) (pullback.snd h (f ≫ g) ≫ f)
    (by exact mapX_condition f g h)

/-- `mapX` commutes with the projections to `B'`. -/
theorem mapX_fst (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    mapX f g h ≫ pullback.fst h g = pullback.fst h (f ≫ g) :=
  sorry

/-- `mapX` commutes with the projections to `Z` via `f`. -/
theorem mapX_snd (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    mapX f g h ≫ pullback.snd h g = pullback.snd h (f ≫ g) ≫ f :=
  sorry

/-- The induced morphism satisfies both projection identities over `B'` and `Z`. -/
theorem mapX_spec (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    mapX f g h ≫ pullback.fst h g = pullback.fst h (f ≫ g) ∧
      mapX f g h ≫ pullback.snd h g = pullback.snd h (f ≫ g) ≫ f :=
  sorry

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
  sorry

/-- `fiberIso` identifies the projections to `Z`. -/
theorem fiberIso_snd (h : B' ⟶ B) (g : Z ⟶ B) {T : Over S} (a' : ofOver T ⟶ B') :
    (fiberIso h g a').hom ≫ fiberSnd g (a' ≫ h) =
      fiberSnd (pullback.fst h g) a' ≫ pullback.snd h g :=
  sorry

private theorem pairMap_overZ (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) {T : Over S}
    (p : Pair (mapX f g h) (pullback.fst h g) T) :
    ((fiberIso h g p.base).inv ≫ p.lift ≫ pullback.snd h (f ≫ g)) ≫ f =
      fiberSnd g (p.base ≫ h) :=
  sorry

/-- The forward transformation sends a pair over `B'` to the pair over `B`
with base `a' ≫ h` and lift transported along `fiberIso`. -/
def pairMap (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) {T : Over S}
    (p : Pair (mapX f g h) (pullback.fst h g) T) : Pair f g T where
  base := p.base ≫ h
  lift := (fiberIso h g p.base).inv ≫ p.lift ≫ pullback.snd h (f ≫ g)
  overZ := by exact pairMap_overZ f g h p

private theorem pairInv_condition (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B)
    {T : Over S} (a' : ofOver T ⟶ B') (q : Pair f g T) (hq : a' ≫ h = q.base) :
    (fiberFst (pullback.fst h g) a' ≫ a') ≫ h =
      ((fiberIso h g a').hom ≫ (eqToHom (congrArg (fiber g) hq) ≫ q.lift)) ≫
        (f ≫ g) :=
  sorry

private def pairInvLift (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) {T : Over S}
    (a' : ofOver T ⟶ B') (q : Pair f g T) (hq : a' ≫ h = q.base) :
    fiber (pullback.fst h g) a' ⟶ pullback h (f ≫ g) :=
  pullback.lift (fiberFst (pullback.fst h g) a' ≫ a')
    ((fiberIso h g a').hom ≫ (eqToHom (congrArg (fiber g) hq) ≫ q.lift))
    (pairInv_condition f g h a' q hq)

private theorem pairInv_overZ (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) {T : Over S}
    (a' : ofOver T ⟶ B') (q : Pair f g T) (hq : a' ≫ h = q.base) :
    pairInvLift f g h a' q hq ≫ mapX f g h = fiberSnd (pullback.fst h g) a' :=
  sorry

/-- The inverse transformation reconstructs a pair over `B'` from a `B'`-point
and a compatible restriction-of-scalars pair over `B`. -/
def pairInv (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) {T : Over S}
    (a' : ofOver T ⟶ B') (q : Pair f g T) (hq : a' ≫ h = q.base) :
    Pair (mapX f g h) (pullback.fst h g) T where
  base := a'
  lift := private pairInvLift f g h a' q hq
  overZ := by exact pairInv_overZ f g h a' q hq

private theorem pairEquiv_left_inv (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B)
    (T : Over S) :
    Function.LeftInverse
      (fun (p : { p : (ofOver T ⟶ B') × Pair f g T // p.1 ≫ h = p.2.base }) ↦
        pairInv f g h p.1.1 p.1.2 p.2)
      (fun (p : Pair (mapX f g h) (pullback.fst h g) T) ↦
        (⟨⟨p.base, pairMap f g h p⟩, rfl⟩ :
          { p : (ofOver T ⟶ B') × Pair f g T // p.1 ≫ h = p.2.base })) :=
  sorry

private theorem pairEquiv_right_inv (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B)
    (T : Over S) :
    Function.RightInverse
      (fun (p : { p : (ofOver T ⟶ B') × Pair f g T // p.1 ≫ h = p.2.base }) ↦
        pairInv f g h p.1.1 p.1.2 p.2)
      (fun (p : Pair (mapX f g h) (pullback.fst h g) T) ↦
        (⟨⟨p.base, pairMap f g h p⟩, rfl⟩ :
          { p : (ofOver T ⟶ B') × Pair f g T // p.1 ≫ h = p.2.base })) :=
  sorry

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
  sorry

/-- The inverse of `pairEquiv` is `pairInv` on a compatible pair of points. -/
theorem pairEquiv_symm_apply (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) {T : Over S}
    (p : (ofOver T ⟶ B') × Pair f g T) (hp : p.1 ≫ h = p.2.base) :
    (pairEquiv f g h T).symm ⟨p, hp⟩ = pairInv f g h p.1 p.2 hp :=
  sorry

private theorem toRestrictionOfScalars_naturality
    (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T') :
    (restrictionOfScalars (mapX f g h) (pullback.fst h g)).map φ ≫
        TypeCat.ofHom (pairMap f g h (T := T'.unop)) =
      TypeCat.ofHom (pairMap f g h (T := T.unop)) ≫
        (restrictionOfScalars f g).map φ :=
  sorry

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
  sorry

private theorem baseChangeInv_compatibility (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B)
    (T : (Over S)ᵒᵖ) (x : (pullback (toSheaf.map h) (toBase f g)).obj.obj T) :
    yonedaEquiv.symm
        ((pullback.fst (toSheaf.map h) (toBase f g)).hom.app T x).down ≫ h =
      ((pullback.snd (toSheaf.map h) (toBase f g)).hom.app T x).base :=
  sorry

private def baseChangeInvApp (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B)
    (T : (Over S)ᵒᵖ) :
    (pullback (toSheaf.map h) (toBase f g)).obj.obj T →
      Pair (mapX f g h) (pullback.fst h g) T.unop :=
  fun x ↦ pairInv f g h
    (yonedaEquiv.symm
      ((pullback.fst (toSheaf.map h) (toBase f g)).hom.app T x).down)
    ((pullback.snd (toSheaf.map h) (toBase f g)).hom.app T x)
    (baseChangeInv_compatibility f g h T x)

private theorem baseChangeInv_naturality (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B)
    {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T') :
    (pullback (toSheaf.map h) (toBase f g)).obj.map φ ≫
        TypeCat.ofHom (baseChangeInvApp f g h T') =
      TypeCat.ofHom (baseChangeInvApp f g h T) ≫
        (restrictionOfScalars (mapX f g h) (pullback.fst h g)).map φ :=
  sorry

private def baseChangeInv (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    pullback (toSheaf.map h) (toBase f g) ⟶
      sheaf (mapX f g h) (pullback.fst h g) :=
  Sheaf.homEquiv.symm
    { app T := TypeCat.ofHom (baseChangeInvApp f g h T)
      naturality := fun _ _ φ ↦ baseChangeInv_naturality f g h φ }

private theorem baseChangeHom_condition (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    toBase (mapX f g h) (pullback.fst h g) ≫ toSheaf.map h =
      toRestrictionOfScalars f g h ≫ toBase f g :=
  sorry

private def baseChangeHom (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    sheaf (mapX f g h) (pullback.fst h g) ⟶
      pullback (toSheaf.map h) (toBase f g) :=
  pullback.lift (toBase (mapX f g h) (pullback.fst h g))
    (toRestrictionOfScalars f g h) (baseChangeHom_condition f g h)

private theorem baseChange_hom_inv_id (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    baseChangeHom f g h ≫ baseChangeInv f g h =
      𝟙 (sheaf (mapX f g h) (pullback.fst h g)) :=
  sorry

private theorem baseChange_inv_hom_id (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    baseChangeInv f g h ≫ baseChangeHom f g h =
      𝟙 (pullback (toSheaf.map h) (toBase f g)) :=
  sorry

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
  sorry

/-- The second projection of `pullbackIso.hom` is `toRestrictionOfScalars`. -/
theorem pullbackIso_hom_snd (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    (pullbackIso f g h).hom ≫ pullback.snd (toSheaf.map h) (toBase f g) =
      toRestrictionOfScalars f g h :=
  sorry

/-- The square of restriction-of-scalars sheaves induced by `B' ⟶ B`
is cartesian in fppf sheaves on schemes over `S`. -/
theorem baseChange_isPullback (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    IsPullback (toBase (mapX f g h) (pullback.fst h g))
      (toRestrictionOfScalars f g h) (toSheaf.map h) (toBase f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars
