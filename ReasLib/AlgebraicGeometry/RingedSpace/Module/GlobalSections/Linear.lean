/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Center.Linear
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Linearity over global sections

The ring of global sections of a ringed space acts canonically on its category of module sheaves.
The action is constructed through the categorical center, so scalar notation is available without
rebuilding local instances in downstream files.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.GlobalSections

variable {X : RingedSpace.{u}}

/-- Restriction of global functions to an open subset. -/
abbrev restrict (X : RingedSpace.{u}) (U : Opens X.carrier) :
    globalSectionsRing X ⟶ sectionsRingOnOpen X U :=
  X.presheaf.map (Opens.leTop U).op

/-- Multiplication by a global function on the sections of a module sheaf over one open. -/
noncomputable abbrev mulApp
    (f : globalSectionsRing X) (M : X.Modules) (U : (Opens X.carrier)ᵒᵖ) :
    M.val.obj U ⟶ M.val.obj U :=
  ModuleCat.ofHom
    (LinearMap.lsmul (X.presheaf.obj U) (M.val.obj U)
      ((restrict X U.unop).hom f))

/-- Multiplication by a global function commutes with restriction maps. -/
theorem mulApp_naturality
    (f : globalSectionsRing X) (M : X.Modules)
    {U V : (Opens X.carrier)ᵒᵖ} (i : U ⟶ V) :
    M.val.map i ≫
        (ModuleCat.restrictScalars ((X.presheaf.map i).hom)).map (mulApp f M V) =
      mulApp f M U ≫ M.val.map i := sorry

/-- Multiplication by a global function as an endomorphism of a module sheaf. -/
@[stacks 0EHA "global-section scalar endomorphism of a module sheaf"]
noncomputable def mul (f : globalSectionsRing X) (M : X.Modules) : M ⟶ M where
  val.app U := mulApp f M U
  val.naturality i := mulApp_naturality f M i

/-- Module-sheaf morphisms commute with multiplication by a global function. -/
theorem mul_naturality
    (f : globalSectionsRing X) {M N : X.Modules} (φ : M ⟶ N) :
    φ ≫ mul f N = mul f M ≫ φ := sorry

/-- A global function determines a central endomorphism of the category of module sheaves. -/
noncomputable def center (f : globalSectionsRing X) : CatCenter X.Modules where
  app M := mul f M
  naturality := fun {M N} φ ↦ mul_naturality f (M := M) (N := N) φ

/-- The unit global function acts as the identity central endomorphism. -/
theorem center_one (X : RingedSpace.{u}) :
    center (1 : globalSectionsRing X) = 1 := sorry

/-- Multiplication of global functions agrees with multiplication in the categorical center. -/
theorem center_mul (f g : globalSectionsRing X) :
    center (f * g) = center f * center g := sorry

/-- The zero global function acts as the zero central endomorphism. -/
theorem center_zero (X : RingedSpace.{u}) :
    center (0 : globalSectionsRing X) = 0 := sorry

/-- Addition of global functions agrees with addition in the categorical center. -/
theorem center_add (f g : globalSectionsRing X) :
    center (f + g) = center f + center g := sorry

/-- The canonical ring homomorphism from global functions to central endomorphisms of module
sheaves. -/
@[stacks 0EHA "global-section action through the categorical center"]
noncomputable def centerHom (X : RingedSpace.{u}) :
    globalSectionsRing X →+* CatCenter X.Modules where
  toFun := center
  map_one' := center_one X
  map_mul' := center_mul
  map_zero' := center_zero X
  map_add' := center_add

/-- The category of module sheaves is canonically linear over the ring of global functions. -/
@[stacks 0EHA "global-section linearity of module sheaves"]
noncomputable instance instLinear (X : RingedSpace.{u}) :
    Linear (globalSectionsRing X) X.Modules :=
  Linear.ofRingMorphism (centerHom X)

/-- Categorical scalar multiplication by a global function is the explicit sectionwise
multiplication endomorphism. -/
@[simp]
theorem smul_id_eq_mul (f : globalSectionsRing X) (M : X.Modules) :
    f • 𝟙 M = mul f M := sorry

end AlgebraicGeometry.RingedSpace.GlobalSections

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- Multiplication by a global section on a module sheaf, exposed at the ringed-space layer. -/
@[stacks 0EHA "global-section multiplication on a module sheaf"]
noncomputable abbrev globalSectionMul (f : globalSectionsRing X) (M : X.Modules) : M ⟶ M :=
  GlobalSections.mul f M

end AlgebraicGeometry.RingedSpace
