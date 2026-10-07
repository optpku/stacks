module

public import ReasLib.CategoryTheory.Abelian.Injective.Coseparator
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
import Mathlib.Tactic.CrossRefAttribute

/-!
# Injective coseparators for abelian sheaves

This leaf records only existence.  It deliberately does not choose a global coseparator: the
choice is noncanonical and should remain an explicit parameter of duality constructions.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.AbelianSheaf

variable {C : Type u} [Category.{v} C]

/-- Abelian sheaves on a site admit an injective coseparator. -/
@[stacks 01DQ "injective abelian-sheaf coseparator"]
theorem nonempty_injectiveCoseparator (J : GrothendieckTopology C) :
    Nonempty
      (InjectiveCoseparator (Sheaf J AddCommGrpCat.{max u v})) := sorry

end CategoryTheory.AbelianSheaf
