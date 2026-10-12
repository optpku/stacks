/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.9.15

@stack 00CU
-/

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]
variable (S : Submonoid R)
variable {M : Type v} [AddCommGroup M] [Module R M]

open Submodule

/- Lemma 10.9.15: for the canonical localization map `M → S⁻¹M`, every submodule of `S⁻¹M`
is the localization of its inverse image in `M`. This is exactly the `l_u_eq` theorem of the
owner Galois insertion `localized'gi` for submodule localization. -/
@[stacks 00CU]
#check (localized'gi (Localization S) S (LocalizedModule.mkLinearMap S M)).l_u_eq

end
