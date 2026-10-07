module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import ReasLib.LinearAlgebra.ExteriorAlgebra.Determinant.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Determinants in `ModuleCat`

This file bundles the algebraic determinant submodule as an object of `ModuleCat`.  It is a thin
categorical facade: all concrete data and universal properties remain owned by
`Module.Determinant`.
@stack 0FJA
@stack 0FJB
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped Module.Determinant

universe u v

namespace ModuleCat.Determinant

variable (R : Type u) [CommRing R]

/-- The determinant submodule of a `ModuleCat R` object, bundled again in `ModuleCat R`.  The
output universe also contains the base ring because the ambient exterior algebra does. -/
@[stacks 0FJA "determinant object in ModuleCat"]
abbrev obj (M : ModuleCat.{v} R) : ModuleCat.{max u v} R :=
  ModuleCat.of R det[R](M)

/-- The exterior algebra of a `ModuleCat R` object, bundled as an ambient module object. -/
@[stacks 0FJA "ambient exterior algebra object in ModuleCat"]
abbrev ambient (M : ModuleCat.{v} R) : ModuleCat.{max u v} R :=
  ModuleCat.of R (ExteriorAlgebra R M)

/-- The determinant inclusion as a morphism in `ModuleCat R`. -/
@[stacks 0FJA "determinant inclusion in ModuleCat"]
abbrev ι (M : ModuleCat.{v} R) : obj R M ⟶ ambient R M :=
  ModuleCat.ofHom (Module.Determinant.ι R M)

/-- A module-object isomorphism induces the corresponding isomorphism of ambient exterior
algebras. -/
@[stacks 0FJB "exterior algebra isomorphism in ModuleCat"]
def ambientIso {M N : ModuleCat.{v} R} (e : M ≅ N) :
    ambient R M ≅ ambient R N :=
  (ExteriorAlgebra.mapEquiv e.toLinearEquiv).toLinearEquiv.toModuleIso

/-- A module-object isomorphism induces a determinant isomorphism in `ModuleCat R`. -/
@[stacks 0FJB "determinant isomorphism in ModuleCat"]
def mapIso {M N : ModuleCat.{v} R} (e : M ≅ N) : obj R M ≅ obj R N :=
  (Module.Determinant.mapIso e.toLinearEquiv).toModuleIso

/-- The forward morphism of the bundled determinant isomorphism is induced by the algebraic
determinant map. -/
@[simp]
theorem mapIso_hom {M N : ModuleCat.{v} R} (e : M ≅ N) :
    (mapIso R e).hom = ModuleCat.ofHom (Module.Determinant.mapIsoHom e.toLinearEquiv) := sorry

/-- The inverse morphism of the bundled determinant isomorphism is induced by the inverse
algebraic determinant map. -/
@[simp]
theorem mapIso_inv {M N : ModuleCat.{v} R} (e : M ≅ N) :
    (mapIso R e).inv = ModuleCat.ofHom (Module.Determinant.mapIsoInv e.toLinearEquiv) := sorry

/-- The determinant isomorphism commutes with the canonical inclusions into the ambient exterior
algebra objects. -/
@[reassoc, stacks 0FJB "determinant isomorphism naturality in ModuleCat"]
theorem mapIso_hom_ι {M N : ModuleCat.{v} R} (e : M ≅ N) :
    (mapIso R e).hom ≫ ι R N = ι R M ≫ (ambientIso R e).hom := sorry

/-- The identity module-object isomorphism induces the identity determinant isomorphism. -/
@[simp]
theorem mapIso_refl (M : ModuleCat.{v} R) :
    mapIso R (Iso.refl M) = Iso.refl (obj R M) := sorry

/-- Bundled determinant isomorphisms respect composition. -/
@[simp]
theorem mapIso_trans {M N P : ModuleCat.{v} R} (e : M ≅ N) (e' : N ≅ P) :
    mapIso R (e.trans e') = (mapIso R e).trans (mapIso R e') := sorry

end ModuleCat.Determinant
