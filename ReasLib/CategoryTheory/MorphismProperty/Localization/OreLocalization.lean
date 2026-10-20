module

public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.GroupTheory.OreLocalization.Basic
public import ReasLib.CategoryTheory.MorphismProperty.SingleObj
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ore localization as categorical localization

For a monoid `R` and a left Ore submonoid `S`, the functor
`SingleObj R ⥤ SingleObj R[S⁻¹]` induced by `OreLocalization.numeratorHom` realizes the
categorical localization at `SingleObj.submonoidProperty S`.

The target monoid and numerator map are the canonical mathlib Ore-localization data; this file
only supplies the bridge to `Functor.IsLocalization`.
-/

@[expose] public section

open CategoryTheory.MorphismProperty
open OreLocalization

universe u

namespace CategoryTheory.SingleObj

variable {R : Type u} [Monoid R]

/-- Remark 4.27.3 (6) (Stacks 0BM1): the functor induced by the Ore-localization monoid
homomorphism is the categorical localization of `SingleObj R` at the morphisms represented by
`S`. -/
@[stacks 0BM1 "Ore localization of a one-object monoid"]
instance oreLocalizationFunctor_isLocalization
    (S : Submonoid R) [OreSet S] :
    ((numeratorHom (R := R) (S := S)).toFunctor :
      SingleObj R ⥤ SingleObj R[S⁻¹]).IsLocalization
        (submonoidProperty S) := sorry
/- Proof strategy: map a functor out of `SingleObj R` to the monoid of endomorphisms of its unique
image object. If it inverts `S`, package those endomorphisms as units and apply
`OreLocalization.universalMulHom`; `universalMulHom_commutes` gives factorization and
`universalMulHom_unique` gives uniqueness, yielding `Functor.IsLocalization.mk'`. -/

end CategoryTheory.SingleObj
