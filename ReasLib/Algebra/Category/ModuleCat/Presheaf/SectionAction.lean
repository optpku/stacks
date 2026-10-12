/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Over
public import ReasLib.Algebra.Category.Ring.Sheaf
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Action of local sections on restricted module presheaves

For a commutative-ring presheaf `O`, a section over `U` acts on the restriction of every
`O`-module presheaf to `C / U`.  The canonical owner is the bundled ring homomorphism
`SectionAction.action`; topology and sheaf conditions play no role in its construction.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w z

namespace PresheafOfModules.SectionAction

variable {C : Type u} [Category.{v} C]
variable (O : Cᵒᵖ ⥤ CommRingCat.{w})
variable (M : PresheafOfModules.{z} (CategoryTheory.Presheaf.ringPresheafOfComm O))

/-- The restriction of a section over `U` to an object of the slice category `C / U`. -/
def restrict (U : C) (r : O.obj (op U)) (V : (Over U)ᵒᵖ) :
    ((Over.forget U).op ⋙ O).obj V :=
  O.map (op V.unop.hom) r

/-- Multiplication by a restricted section as a linear endomorphism at one slice object. -/
noncomputable def app (U : C) (r : O.obj (op U)) (V : (Over U)ᵒᵖ) :
    (M.over U).obj V ⟶ (M.over U).obj V :=
  ModuleCat.ofHom (LinearMap.lsmul _ _ (restrict O U r V))

/-- Evaluation of the objectwise section action is scalar multiplication by the restricted
section. -/
@[simp]
theorem app_apply (U : C) (r : O.obj (op U)) (V : (Over U)ᵒᵖ)
    (x : (M.over U).obj V) :
    app O M U r V x = restrict O U r V • x := sorry

/-- Objectwise multiplication by a restricted section commutes with the restriction maps of
the module presheaf on `C / U`. -/
theorem app_naturality (U : C) (r : O.obj (op U))
    {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y) :
    (M.over U).map f ≫
        (ModuleCat.restrictScalars
          (((Over.forget U).op ⋙
            CategoryTheory.Presheaf.ringPresheafOfComm O).map f).hom).map
          (app O M U r Y) =
      app O M U r X ≫ (M.over U).map f := sorry

/-- Multiplication by one section as an endomorphism of the restricted module presheaf. -/
noncomputable def hom (U : C) (r : O.obj (op U)) : M.over U ⟶ M.over U where
  app V := app O M U r V
  naturality f := app_naturality O M U r f

/-- The component of the section-action endomorphism is the canonical objectwise scalar
multiplication map. -/
@[simp]
theorem hom_app (U : C) (r : O.obj (op U)) (V : (Over U)ᵒᵖ) :
    (hom O M U r).app V = app O M U r V := sorry

/-- The zero section acts by the zero endomorphism. -/
@[simp]
theorem hom_zero (U : C) : hom O M U 0 = 0 := sorry

/-- The action is additive in the section. -/
theorem hom_add (U : C) (r s : O.obj (op U)) :
    hom O M U (r + s) = hom O M U r + hom O M U s := sorry

/-- The unit section acts by the identity endomorphism. -/
@[simp]
theorem hom_one (U : C) : hom O M U 1 = 𝟙 _ := sorry

/-- Multiplication of sections is composition in the endomorphism ring. -/
theorem hom_mul (U : C) (r s : O.obj (op U)) :
    hom O M U (r * s) = hom O M U s ≫ hom O M U r := sorry

/-- Local sections act canonically on the restriction of a module presheaf to the slice
category. -/
@[stacks 03EM "local-section action"]
noncomputable def action (U : C) : O.obj (op U) →+* End (M.over U) where
  toFun := hom O M U
  map_one' := hom_one O M U
  map_zero' := hom_zero O M U
  map_mul' := hom_mul O M U
  map_add' := hom_add O M U

/-- The bundled local-section action evaluates to restricted scalar multiplication. -/
@[simp]
theorem action_app_apply (U : C) (r : O.obj (op U)) (V : (Over U)ᵒᵖ)
    (x : (M.over U).obj V) :
    ((action O M U r).app V) x = restrict O U r V • x := sorry


-- The non-Prop payload of `action` is the explicit objectwise `LinearMap.lsmul` above.
-- Any `sorryAx` is confined to naturality and ring-homomorphism law fields.

end PresheafOfModules.SectionAction
