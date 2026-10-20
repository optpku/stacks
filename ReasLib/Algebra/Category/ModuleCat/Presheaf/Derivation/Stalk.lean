module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Stalk
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Stalks of presheaf derivations

A compatible family of relative derivations on a topological space induces a derivation on every
stalk.  The underlying additive map is obtained directly from the filtered-colimit presentation
of the stalk.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace PresheafOfModules.Derivation'

variable {X : TopCat.{u}}
variable {S R : X.Presheaf CommRingCat.{u}}
variable {M : PresheafOfModules
  (CategoryTheory.Presheaf.ringPresheafOfComm R)}
variable {φ : S ⟶ R} (D : M.Derivation' φ) (x : X)

/-- The map from the additive group of one neighborhood section ring to the stalk of the target
module, obtained by applying the derivation and then taking its germ. -/
noncomputable def stalkCoconeLeg (U : (OpenNhds x)ᵒᵖ) :
    (((OpenNhds.inclusion x).op ⋙ R ⋙
      (forget₂ CommRingCat RingCat.{u} ⋙
        forget₂ RingCat AddCommGrpCat.{u})).obj U) ⟶
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x :=
  AddCommGrpCat.ofHom D.d ≫
    TopCat.Presheaf.germ M.presheaf U.unop.1 x U.unop.2

/-- The neighborhood maps defining `stalkCoconeLeg` are compatible with restriction. -/
theorem stalkCoconeLeg_naturality {U V : (OpenNhds x)ᵒᵖ} (i : U ⟶ V) :
    (((OpenNhds.inclusion x).op ⋙ R ⋙
      (forget₂ CommRingCat RingCat.{u} ⋙
        forget₂ RingCat AddCommGrpCat.{u})).map i) ≫
        stalkCoconeLeg D x V =
      stalkCoconeLeg D x U := sorry

/-- The cocone of local derivations with values in the module stalk. -/
noncomputable def stalkCocone :
    Cocone ((OpenNhds.inclusion x).op ⋙ R ⋙
      (forget₂ CommRingCat RingCat.{u} ⋙
        forget₂ RingCat AddCommGrpCat.{u})) where
  pt := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x
  ι :=
    { app := stalkCoconeLeg D x
      naturality := fun _ _ i ↦ stalkCoconeLeg_naturality D x i }

/-- The additive map on stalks induced by a presheaf derivation. -/
noncomputable def stalkAddMap :
    (forget₂ CommRingCat RingCat.{u} ⋙
        forget₂ RingCat AddCommGrpCat.{u}).obj (R.stalk x) ⟶
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x :=
  (preservesColimitIso
      (forget₂ CommRingCat RingCat.{u} ⋙
        forget₂ RingCat AddCommGrpCat.{u})
      ((OpenNhds.inclusion x).op ⋙ R)).hom ≫
    colimit.desc _ (stalkCocone D x)

/-- The stalk map induced by a derivation preserves addition. -/
theorem stalkAddMap_add (a b : R.stalk x) :
    stalkAddMap D x (a + b) = stalkAddMap D x a + stalkAddMap D x b := sorry

/-- The stalk map induced by a derivation satisfies the Leibniz rule. -/
theorem stalkAddMap_mul (a b : R.stalk x) :
    stalkAddMap D x (a * b) =
      a • stalkAddMap D x b + b • stalkAddMap D x a := sorry

/-- The stalk map induced by a relative derivation vanishes on the base-ring stalk. -/
theorem stalkAddMap_base (a : S.stalk x) :
    stalkAddMap D x ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ a) = 0 := sorry

/-- The derivation on stalks induced by a presheaf relative derivation. -/
noncomputable def stalk :
    (PresheafOfModules.stalkModuleCatOfCommRing M x).Derivation
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ) :=
  ModuleCat.Derivation.mk (stalkAddMap D x)
    (stalkAddMap_add D x) (stalkAddMap_mul D x) (stalkAddMap_base D x)

/-- Taking the stalk derivation sends the germ of a section to the germ of its derivative. -/
theorem stalk_d_germ (U : Opens X) (hx : x ∈ U) (r : R.obj (Opposite.op U)) :
    (stalk D x).d (R.germ U x hx r) =
      TopCat.Presheaf.germ M.presheaf U x hx (D.d r) := sorry

end PresheafOfModules.Derivation'
