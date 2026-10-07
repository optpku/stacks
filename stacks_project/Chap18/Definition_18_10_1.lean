module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
import StacksCheckRecall

/-!
# Definition 18.10.1

The category of module sheaves is already the canonical Mathlib category `SheafOfModules`.
-/

@[expose] public section

open CategoryTheory

universe z w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (𝒪 : Sheaf J RingCat.{w})

/- Definition 18.10.1 (03CW): sheaves of modules over a ring sheaf `𝒪` form the canonical
category `SheafOfModules 𝒪`. -/
@[stacks 03CW]
#check (SheafOfModules.{z} 𝒪 : Type _)

variable (ℱ 𝒢 : SheafOfModules.{z} 𝒪)

/- Morphisms of module sheaves are the morphisms in this canonical category. -/
#check (ℱ ⟶ 𝒢)

/- The canonical forgetful functor remembers the underlying module presheaf. -/
#check (SheafOfModules.forget.{z} 𝒪)

/- The canonical additive forgetful functor remembers the underlying sheaf of abelian groups. -/
#check (SheafOfModules.toSheaf.{z} 𝒪)
