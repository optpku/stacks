module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.DeRham
public import ReasLib.RingTheory.Kaehler.DeRham.Wedge
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-!
# Wedge multiplication on presheaves of relative differential forms

Objectwise wedge products on relative differential forms commute with restriction maps and
therefore assemble into morphisms of module presheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace PresheafOfModules.DeRham

variable {C : Type u} [Category.{v} C]
variable {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{max u v}}

/-- Objectwise relative-form wedge products commute with restriction maps. -/
theorem formWedge_app_naturality (φ : O₁ ⟶ O₂) (p q : ℕ)
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    (PresheafOfModules.Monoidal.tensorObj (form φ p) (form φ q)).map i ≫
        (ModuleCat.restrictScalars ((ringPresheaf O₂).map i).hom).map
          (CommRingCat.DeRham.formWedge (φ.app V) p q) =
      CommRingCat.DeRham.formWedge (φ.app U) p q ≫ (form φ (p + q)).map i := sorry

/-- The canonical wedge product on presheaves of relative forms. -/
noncomputable def formWedge (φ : O₁ ⟶ O₂) (p q : ℕ) :
    PresheafOfModules.Monoidal.tensorObj (form φ p) (form φ q) ⟶
      form φ (p + q) where
  app U := CommRingCat.DeRham.formWedge (φ.app U) p q
  naturality i := formWedge_app_naturality φ p q i

/-- The component of the presheaf wedge is the algebraic relative-form wedge. -/
theorem formWedge_app (φ : O₁ ⟶ O₂) (p q : ℕ) (U : Cᵒᵖ) :
    (formWedge φ p q).app U = CommRingCat.DeRham.formWedge (φ.app U) p q := sorry

end PresheafOfModules.DeRham
