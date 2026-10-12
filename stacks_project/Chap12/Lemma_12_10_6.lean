/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Abelian.SerreQuotient
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe uA vA uB vB

namespace CategoryTheory.ObjectProperty.SerreClassLocalization

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (P : ObjectProperty A) [P.IsSerreClass]

/- Lemma 12.10.6 [02MS]: the canonical localization at a Serre class is abelian, and the
localization functor is exact with kernel `P`. -/
#check (inferInstance : Abelian P.isoModSerre.Localization)
#check (quotientExactFunctor P : A ⥤ₑ P.isoModSerre.Localization)
#check (quotientKernel_eq P : (quotientExactFunctor P).obj.kernel = P)

/- Lemma 12.10.6 [02MS]: the canonical quotient functor is essentially surjective. -/
@[stacks 02MS]
#check (Localization.essSurj P.isoModSerre.Q P.isoModSerre :
  Functor.EssSurj P.isoModSerre.Q)

variable (B : Type uB) [Category.{vB} B] [Abelian B] (G : A ⥤ₑ B)

/- Lemma 12.10.6 [02MS]: an exact functor factors through the Serre quotient exactly when its
kernel contains `P`. -/
@[stacks 02MS]
#check (exactFunctor_mem_essImage_iff P G :
  (whiskeringLeft P.isoModSerre.Q P B).essImage G ↔ P ≤ G.obj.kernel)

end CategoryTheory.ObjectProperty.SerreClassLocalization
