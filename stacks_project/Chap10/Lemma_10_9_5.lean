module

public import ReasLib.Algebra.Category.ModuleCat.Localization.Equivalence
import StacksCheckRecall

/-!
# Modules over a Localization

Lemma 10.9.5 is the canonical equivalence between modules over `S⁻¹R` and
`R`-modules on which `S` acts invertibly.

@stack 07JY
-/

@[expose] public section

open CategoryTheory

universe u v

section

variable {R : Type u} [CommRing R] (S : Submonoid R)

@[stacks 07JY]
#check (ModuleCat.Localization.equivalence S (Localization S) :
  ModuleCat.{v} (Localization S) ≌
    ObjectProperty.FullSubcategory
      (fun M : ModuleCat.{v} R ↦
        ∀ s : S, IsUnit (algebraMap R (Module.End R M) s)))

@[stacks 07JY "localized identity criterion"]
#check @ModuleCat.Localization.isLocalizedModule_id_iff

end
