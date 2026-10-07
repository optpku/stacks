module

public import ReasLib.CategoryTheory.Abelian.GrothendieckAxioms.Representable
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.IsGrothendieckAbelian.Representable

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]

/- Lemma 19.13.1: a set-valued presheaf on a Grothendieck abelian category commutes
with colimits precisely when it is representable. In Lean this is the equivalent
limit-preservation statement on `Aᵒᵖ`. -/
@[stacks 07D7] #check
  (iff_preservesLimits :
    ∀ F : Aᵒᵖ ⥤ Type v, F.IsRepresentable ↔ CategoryTheory.Limits.PreservesLimits F)

end CategoryTheory.IsGrothendieckAbelian.Representable
