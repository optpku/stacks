/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
import StacksCheckRecall

/-!
# Definition 18.9.1

The category, objects, and morphisms of module presheaves are already the canonical Mathlib
category `PresheafOfModules`.
-/

@[expose] public section

open CategoryTheory

universe z w v u

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Cᵒᵖ ⥤ RingCat.{w})

/- Definition 18.9.1 (03CT): presheaves of modules over a ring-valued presheaf `𝒪` form the
canonical category `PresheafOfModules 𝒪`. -/
@[stacks 03CT]
#check (PresheafOfModules.{z} 𝒪 : Type _)

variable (ℱ 𝒢 : PresheafOfModules.{z} 𝒪)

/- Morphisms of module presheaves are the morphisms in this canonical category. -/
#check (ℱ ⟶ 𝒢)

/- Forgetting the module structure gives the underlying presheaf of abelian groups. -/
#check (PresheafOfModules.toPresheaf.{z} 𝒪)
