/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (P : ObjectProperty C)

/- Lemma 12.10.2 [02MP]: the closure-based canonical Serre-class structure is equivalent to
the textbook condition on every exact three-term sequence. Strict fullness is inherent in the
`ObjectProperty.FullSubcategory` model. -/
@[stacks 02MP]
#check (P.isSerreClass_iff_exact :
  P.IsSerreClass ↔
    P.Nonempty ∧
      ∀ (S : ShortComplex C), S.Exact → P S.X₁ → P S.X₃ → P S.X₂)

variable [P.IsSerreClass]

/- The associated full subcategory is abelian. -/
#check (inferInstance : Abelian P.FullSubcategory)

/- Its canonical inclusion into the ambient category is exact. -/
#check (IsWeakSerreClass.Inclusion.isExact P :
  exactFunctor P.FullSubcategory C P.ι)

end CategoryTheory.ObjectProperty
