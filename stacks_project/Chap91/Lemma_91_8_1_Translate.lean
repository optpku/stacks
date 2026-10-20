module

public import stacks_project.Chap91.Lemma_91_8_1_Lift
public import stacks_project.Chap91.Lemma_91_7_3_Translate

/-!
# Translation of a flat first-order scheme lift by an Ext¹ class

Given a flat lift `L` and a class `ξ` in `Ext¹(NL[X/S], f^* 𝒞_{S/S'})`, the
pushout translate of the associated 91.7.0.1 solution is rebundled as a scheme
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

/-- The locally ringed space underlying the pushout translate of a flat lift along
an Ext¹ class, obtained by copying the sheafed space of the ringed-space
translate. -/
def translateLocallyRingedSpace (ξ : extOneNL t f) (L : FlatLift t f) :
    LocallyRingedSpace.{u} where
  toSheafedSpace := (Solution.translate ξ (toSolution L)).space
  isLocalRing := sorry

/-- The scheme underlying the pushout translate of a flat lift along an Ext¹ class. -/
def translateSpace (ξ : extOneNL t f) (L : FlatLift t f) : Scheme.{u} where
  toLocallyRingedSpace := translateLocallyRingedSpace ξ L
  local_affine := sorry

/-- The closed-fibre morphism of the translated lift, as a locally ringed-space
morphism. -/
def translateILRS (ξ : extOneNL t f) (L : FlatLift t f) :
    X.toLocallyRingedSpace ⟶ translateLocallyRingedSpace ξ L :=
  LocallyRingedSpace.homMk (Solution.translate ξ (toSolution L)).i sorry

/-- The closed-fibre morphism `X ⟶ X'_ξ` of the translated lift. -/
def translateI (ξ : extOneNL t f) (L : FlatLift t f) :
    X ⟶ translateSpace ξ L :=
  ⟨translateILRS ξ L⟩

/-- The ambient morphism of the translated lift, as a locally ringed-space
morphism. -/
def translateF'LRS (ξ : extOneNL t f) (L : FlatLift t f) :
    translateLocallyRingedSpace ξ L ⟶ S'.toLocallyRingedSpace :=
  LocallyRingedSpace.homMk (Solution.translate ξ (toSolution L)).f' sorry

/-- The ambient morphism `X'_ξ ⟶ S'` of the translated lift. -/
def translateF' (ξ : extOneNL t f) (L : FlatLift t f) :
    translateSpace ξ L ⟶ S' :=
  ⟨translateF'LRS ξ L⟩

/-- The translated ambient morphism is flat. -/
instance instFlat_translateF' (ξ : extOneNL t f) (L : FlatLift t f) :
    Flat (translateF' ξ L) := sorry

/-- The translated square is cartesian. -/
theorem translate_isPullback (ξ : extOneNL t f) (L : FlatLift t f) :
    IsPullback f (translateI ξ L) t (translateF' ξ L) := sorry

/-- Pushout translate of a flat lift along an Ext¹ class, rebundling the
ringed-space translate of `toSolution L` as a scheme. -/
def translate (ξ : extOneNL t f) (L : FlatLift t f) : FlatLift t f :=
  of (translateF' ξ L) (translateI ξ L) (translate_isPullback ξ L)

/-- `translate ξ L` has ambient space the rebundled pushout scheme and closed-fibre
morphism `translateI ξ L`. -/
theorem translate_spec (ξ : extOneNL t f) (L : FlatLift t f) :
    (translate ξ L).space = translateSpace ξ L ∧
      (translate ξ L).f' = translateF' ξ L ∧
        (translate ξ L).i = translateI ξ L := sorry

end FlatLift
end AlgebraicGeometry.Scheme.Thickening
