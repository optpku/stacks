module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Tactic.CrossRefAttribute

/-!
# Binary biproducts of sheaves of modules

In the preadditive category of sheaves of modules, every chosen binary coproduct canonically
determines a binary biproduct.  Registering that construction here lets downstream sheaf APIs ask
only for the colimit data from which their biproduct notation is obtained.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w x

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}} {M N : SheafOfModules.{x} R}

/-- A binary coproduct of sheaves of modules carries its canonical preadditive binary biproduct
structure. -/
@[stacks 0B38 "binary biproduct of module sheaves"]
instance hasBinaryBiproduct [HasBinaryCoproduct M N] : HasBinaryBiproduct M N :=
  HasBinaryBiproduct.of_hasBinaryCoproduct M N

end SheafOfModules
