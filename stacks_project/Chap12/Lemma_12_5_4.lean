module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Balanced
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {X Y : C} (f : X ⟶ Y)

/- Lemma 12.5.4 (1) [010C]: vanishing of the kernel is equivalent to the canonical categorical
predicate `Mono f`. -/
@[stacks 010C]
#check (Preadditive.mono_iff_isZero_kernel f : Mono f ↔ IsZero (kernel f))

/- Lemma 12.5.4 (2) [010C]: dually, vanishing of the cokernel is equivalent to `Epi f`. -/
#check (Preadditive.epi_iff_isZero_cokernel f : Epi f ↔ IsZero (cokernel f))

/- Lemma 12.5.4 (3) [010C]: an abelian category is balanced, so a morphism is an isomorphism
exactly when it is both mono and epi. -/
#check (isIso_iff_mono_and_epi f : IsIso f ↔ Mono f ∧ Epi f)

end
