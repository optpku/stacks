/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Abelian.Injective.Generator
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
variable {U I : C} (hU : IsSeparator U)

/- Lemma 19.11.6: in a Grothendieck abelian category with generator `U`, an object `I` is
injective exactly when every map from a subobject of `U` to `I` extends to `U`. -/
@[stacks 079G] #check
  (Generator.HasSubobjectExtension.injective_iff (I := I) hU :
    Injective I ↔
      ∀ (M : Subobject U) (φ : (M : C) ⟶ I),
        ∃ ψ : U ⟶ I, M.arrow ≫ ψ = φ)

#check @Generator.HasSubobjectExtension
#check @Generator.HasSubobjectExtension.iff_rlp_zero
#check @Generator.HasSubobjectExtension.iff_rlp_monomorphisms_zero
