/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Injective.Localization
import StacksCheckRecall

universe u v

/- Lemma 47.3.8: If `R` is Noetherian and `E` is an injective `R`-module, then
the localization of `E` at a submonoid `S` is injective over the localization
of `R` at `S`. -/
@[stacks 0A6I] #check (Module.Injective.localizedModule :
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (S : Submonoid R)
    (E : Type v) [Small.{v} R] [AddCommGroup E] [Module R E] [Module.Injective R E],
    Module.Injective (Localization S) (LocalizedModule S E))
