module

public import ReasLib.CategoryTheory.Homology.ExactCouple.Shifted.ZeroPage
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (S T : C ≌ C)

/- Remark 12.22.6 (Variant) (1) [0AMK]: the source assumes commuting shift equivalences. A
natural isomorphism is the categorical replacement for literal equality of the two composites. -/
@[stacks 0AMK "(1)"]
#check (S.functor ⋙ T.functor ≅ T.functor ⋙ S.functor)

/- Remark 12.22.6 (Variant) (2) [0AMK]: pairs `(A, d)` with shifted square-zero differential
are represented by the reusable shifted-differential-object owner. -/
@[stacks 0AMK "(2)"]
#check (ShiftedDifferentialObject S.functor)

variable (Q : ShiftedDifferentialObject S.functor)

/- Remark 12.22.6 (Variant) (3) [0AMK]: shifted homology is the homology of the canonical short
complex `S⁻¹Q ⟶ Q ⟶ SQ`. -/
@[stacks 0AMK "(3)"]
#check (Q.homology : C)

variable (K : ShiftedExactCouple.Derived.Construction T)
variable (X : ShiftedExactCouple (S.trans T) T)

/- Remark 12.22.6 (Variant) (4) [0AMK]: the exact couple has shifts `T ∘ S` and `T`, so its
positive pages carry shifts `T^r ∘ S`. -/
@[stacks 0AMK "(4)"]
#check (K.associatedSpectralSequence X :
  ShiftedSpectralSequence (ShiftedSpectralSequence.pageShift (S.trans T) T))

/- Remark 12.22.6 (Variant) (5) [0AMK]: a specified `S⁻¹Q` zeroth page can be adjoined to
the associated shifted spectral sequence. -/
@[stacks 0AMK "(5)"]
#check (ShiftedExactCouple.ZeroPage.page K X Q :
  (r : ℕ) → ShiftedDifferentialObject
    ((ShiftedSpectralSequence.zeroPageShift S T r).functor))
#check (ShiftedSpectralSequence.ZeroPageShift.zero S T :
  ShiftedSpectralSequence.zeroPageShift S T 0 = S)
#check (ShiftedSpectralSequence.ZeroPageShift.one S T :
  ShiftedSpectralSequence.zeroPageShift S T 1 = S.trans T)
#check (ShiftedSpectralSequence.ZeroPageShift.eq_trans_pow S T :
  ∀ r : ℕ, ShiftedSpectralSequence.zeroPageShift S T r = S.trans (T ^ (r : ℤ)))

variable (e : X.E ≅ Q.previousPage.homology)

/- Remark 12.22.6 (Variant) (6) [0AMK]: the page-one comparison identifies `E₁` with the
inverse shift of `H(Q)`. -/
@[stacks 0AMK "(6)"]
#check (ShiftedExactCouple.ZeroPage.page_one_obj K X Q :
  (ShiftedExactCouple.ZeroPage.page K X Q 1).obj = X.E)
#check (ShiftedExactCouple.ZeroPage.homologyIso X Q e :
  X.E ≅ S.functor.inv.obj Q.homology)

/- Remark 12.22.6 (Variant) (7) [0AMK]: the cycle filtration on the zeroth page is pulled back
from the canonical positive-page filtration. -/
@[stacks 0AMK "(7)"]
#check ShiftedExactCouple.ZeroPage.cycle K X Q e

/- Remark 12.22.6 (Variant) (8) [0AMK]: the boundary filtration on the zeroth page is pulled back
from the canonical positive-page filtration. -/
@[stacks 0AMK "(8)"]
#check ShiftedExactCouple.ZeroPage.boundary K X Q e

end CategoryTheory
