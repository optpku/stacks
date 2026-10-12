/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.Algebra.Category.Ring.Sheaf.LocallyRinged
import Mathlib.Tactic.CrossRefAttribute

/-!
# Localization of locally ringed sheaves

Restriction to the slice site over an object preserves the locally ringed condition.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.Sheaf.IsLocallyRinged

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type (max u v))]
variable [J.HasSheafCompose (forget CommRingCat.{max u v})]

/-- Lemma 18.40.12 (04IH) (1): the restriction of a locally ringed sheaf to a slice site is
locally ringed. -/
@[stacks 04IH "(1)"]
theorem over (𝒪 : Sheaf J CommRingCat.{max u v}) [𝒪.IsLocallyRinged] (U : C)
    [HasWeakSheafify (J.over U) (Type (max u v))]
    [(J.over U).HasSheafCompose (forget CommRingCat.{max u v})] :
    (𝒪.over U).IsLocallyRinged := sorry

end CategoryTheory.Sheaf.IsLocallyRinged
