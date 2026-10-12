/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Additive retractions of extension of scalars

This file constructs the additive retraction of extension of scalars along a ring
homomorphism equipped with a retraction.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open scoped ChangeOfRings TensorProduct

namespace ModuleCat.ExtendScalars

/-- Extension of scalars along a split ring homomorphism admits an additive retraction. -/
def addRetraction {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (g : B →+* A) (h : g.comp f = RingHom.id A)
    (M : ModuleCat.{u} A) :
    AddCommGrpCat.of (ModuleCat.ExtendScalars.obj' f M) ⟶ AddCommGrpCat.of M :=
  (forget₂ (ModuleCat B) AddCommGrpCat).map
      ((ModuleCat.extendRestrictScalarsAdj g).unit.app
        (ModuleCat.ExtendScalars.obj' f M)) ≫
    (forget₂ (ModuleCat A) AddCommGrpCat).map
      ((ModuleCat.extendScalarsComp f g).inv.app M) ≫
    (forget₂ (ModuleCat A) AddCommGrpCat).map
      (eqToIso (congrArg (fun φ ↦ ModuleCat.ExtendScalars.obj' φ M) h)).hom ≫
    (forget₂ (ModuleCat A) AddCommGrpCat).map
      ((ModuleCat.extendScalarsId A).hom.app M)

/-- On a pure tensor, the additive retraction applies the ring retraction to the scalar. -/
theorem addRetraction_tmul {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (g : B →+* A) (h : g.comp f = RingHom.id A)
    (M : ModuleCat.{u} A) (b : B) (m : M) :
    addRetraction f g h M (b ⊗ₜ[A, f] m) = g b • m := sorry

end ModuleCat.ExtendScalars
