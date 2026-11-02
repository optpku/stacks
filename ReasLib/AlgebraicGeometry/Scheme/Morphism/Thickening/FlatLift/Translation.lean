/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.FlatLift
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution.Torsor

/-!
# Translation of a flat first-order scheme lift by an Ext¹ class

Given a flat lift `L` and a class `ξ` in `Ext¹(NL[X/S], f^* 𝒞_{S/S'})`, the
pushout translate of the associated ringed-space solution is rebundled as a scheme
with the same sheafed space.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Thickening
open AlgebraicGeometry.RingedSpace.Thickening (Solution)
open scoped AlgebraicGeometry DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Thickening
namespace FlatLift

variable {S S' X : Scheme.{u}}
variable {t : S ⟶ S'} [IsFirstOrderThickening t] {f : X ⟶ S} [Flat f]

-- Local declaration justification (module visibility): export this private dependency
-- so the dependent public constructions can use it without publishing its name.
set_option backward.privateInPublic true in
/-- Every stalk of the translated ringed space is a local ring. -/
private theorem translate_isLocalRing (ξ : extOneNL t f) (L : FlatLift t f) :
    ∀ x, IsLocalRing ((Solution.translate ξ (toSolution L)).space.presheaf.stalk x) := sorry

-- Local declaration justification (module visibility): this dependent public construction
-- needs its private implementation certificates available during elaboration.
set_option backward.privateInPublic true in
/-- The locally ringed space underlying the pushout translate of a flat lift along
an Ext¹ class, obtained by copying the sheafed space of the ringed-space
translate. -/
def translateLocallyRingedSpace (ξ : extOneNL t f) (L : FlatLift t f) :
    LocallyRingedSpace.{u} where
  toSheafedSpace := (Solution.translate ξ (toSolution L)).space
  isLocalRing := translate_isLocalRing ξ L

-- Local declaration justification (module visibility): export this private dependency
-- so the dependent public constructions can use it without publishing its name.
set_option backward.privateInPublic true in
/-- The translated locally ringed space is locally affine. -/
private theorem translate_localAffine (ξ : extOneNL t f) (L : FlatLift t f) :
    ∀ x : translateLocallyRingedSpace ξ L,
      ∃ (U : TopologicalSpace.OpenNhds x) (R : CommRingCat.{u}),
        Nonempty ((translateLocallyRingedSpace ξ L).restrict U.isOpenEmbedding ≅
          Spec.toLocallyRingedSpace.obj (Opposite.op R)) := sorry

-- Local declaration justification (module visibility): this dependent public construction
-- needs its private implementation certificates available during elaboration.
set_option backward.privateInPublic true in
/-- The scheme underlying the pushout translate of a flat lift along an Ext¹ class. -/
def translateSpace (ξ : extOneNL t f) (L : FlatLift t f) : Scheme.{u} where
  toLocallyRingedSpace := translateLocallyRingedSpace ξ L
  local_affine := translate_localAffine ξ L

-- Local declaration justification (module visibility): export this private dependency
-- so the dependent public constructions can use it without publishing its name.
set_option backward.privateInPublic true in
/-- The translated closed-fibre map is local on stalks. -/
private theorem translateI_isLocal (ξ : extOneNL t f) (L : FlatLift t f) :
    ∀ x : X, IsLocalHom (((Solution.translate ξ (toSolution L)).i.hom.stalkMap x).hom) := sorry

-- Local declaration justification (module visibility): this dependent public construction
-- needs its private implementation certificates available during elaboration.
set_option backward.privateInPublic true in
/-- The closed-fibre morphism of the translated lift, as a locally ringed-space
morphism. -/
def translateILRS (ξ : extOneNL t f) (L : FlatLift t f) :
    X.toLocallyRingedSpace ⟶ translateLocallyRingedSpace ξ L :=
  LocallyRingedSpace.homMk (Solution.translate ξ (toSolution L)).i (translateI_isLocal ξ L)

/-- The closed-fibre morphism `X ⟶ X'_ξ` of the translated lift. -/
def translateI (ξ : extOneNL t f) (L : FlatLift t f) :
    X ⟶ translateSpace ξ L :=
  ⟨translateILRS ξ L⟩

-- Local declaration justification (module visibility): export this private dependency
-- so the dependent public constructions can use it without publishing its name.
set_option backward.privateInPublic true in
/-- The translated ambient map is local on stalks. -/
private theorem translateF'_isLocal (ξ : extOneNL t f) (L : FlatLift t f) :
    ∀ x : translateLocallyRingedSpace ξ L,
      IsLocalHom (((Solution.translate ξ (toSolution L)).f'.hom.stalkMap x).hom) := sorry

-- Local declaration justification (module visibility): this dependent public construction
-- needs its private implementation certificates available during elaboration.
set_option backward.privateInPublic true in
/-- The ambient morphism of the translated lift, as a locally ringed-space
morphism. -/
def translateF'LRS (ξ : extOneNL t f) (L : FlatLift t f) :
    translateLocallyRingedSpace ξ L ⟶ S'.toLocallyRingedSpace :=
  LocallyRingedSpace.homMk (Solution.translate ξ (toSolution L)).f' (translateF'_isLocal ξ L)

/-- The ambient morphism `X'_ξ ⟶ S'` of the translated lift. -/
def translateF' (ξ : extOneNL t f) (L : FlatLift t f) :
    translateSpace ξ L ⟶ S' :=
  ⟨translateF'LRS ξ L⟩

/-- The translated ambient morphism is flat. -/
theorem translateF'_flat (ξ : extOneNL t f) (L : FlatLift t f) :
    Flat (translateF' ξ L) := sorry

/-- The translated square is cartesian. -/
theorem translate_isPullback (ξ : extOneNL t f) (L : FlatLift t f) :
    IsPullback f (translateI ξ L) t (translateF' ξ L) := sorry

/-- Pushout translate of a flat lift along an Ext¹ class, rebundling the
ringed-space translate of `toSolution L` as a scheme. -/
def translate (ξ : extOneNL t f) (L : FlatLift t f) : FlatLift t f :=
  { space := translateSpace ξ L
    f' := translateF' ξ L
    flat := translateF'_flat ξ L
    i := translateI ξ L
    isPullback := translate_isPullback ξ L }

/-- `translate ξ L` has ambient space the rebundled pushout scheme and closed-fibre
morphism `translateI ξ L`. -/
theorem translate_spec (ξ : extOneNL t f) (L : FlatLift t f) :
    (translate ξ L).space = translateSpace ξ L ∧
      (translate ξ L).f' = translateF' ξ L ∧
        (translate ξ L).i = translateI ξ L := by
  exact ⟨rfl, rfl, rfl⟩

end FlatLift
end AlgebraicGeometry.Scheme.Thickening
