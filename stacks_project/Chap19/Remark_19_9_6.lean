/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Exact.SheafYoneda
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u v

noncomputable section

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasFiniteProducts A]
  (E : ExactStructure A)

/- Remark 19.9.6 (1): an exact structure specifies admissible kernel-cokernel pairs and their
closure under isomorphisms, compositions, pushouts, and pullbacks. -/
@[stacks 05SF "exact structure"] #check
  (E : ExactStructure A)

/- Remark 19.9.6 (2): singleton admissible epimorphisms generate a Grothendieck topology. -/
@[stacks 05SF "admissible-epimorphism topology"] #check
  (E.topology : GrothendieckTopology A)

/- Remark 19.9.6 (3): the additive Yoneda functor lifts to sheaves on that topology. -/
@[stacks 05SF "sheaf-valued Yoneda embedding"] #check
  (E.sheafYoneda : A ⥤ Sheaf E.topology AddCommGrpCat.{v})

/- Remark 19.9.6 (4): the sheaf-valued Yoneda embedding is fully faithful. -/
@[stacks 05SF "fully faithful sheaf-valued Yoneda embedding"] #check
  (inferInstance : Functor.Full E.sheafYoneda)

@[stacks 05SF "fully faithful sheaf-valued Yoneda embedding"] #check
  (inferInstance : Functor.Faithful E.sheafYoneda)

/- Remark 19.9.6 (5): admissible pairs are exactly the pairs mapped to short exact sequences. -/
@[stacks 05SF "admissibility detected by sheaf-valued Yoneda"] #check
  (E.sheafYoneda_shortExact_iff :
    ∀ {S : ShortComplex A}, (S.map E.sheafYoneda).ShortExact ↔ E.admissible S)

/- Remark 19.9.6 (6): the essential image is closed under extensions. -/
@[stacks 05SF "extension-closed sheaf-valued Yoneda image"] #check
  fun {S : ShortComplex (Sheaf E.topology AddCommGrpCat.{v})}
      (hS : S.ShortExact) (h₁ : E.sheafYoneda.essImage S.X₁)
      (h₃ : E.sheafYoneda.essImage S.X₃) ↦
    (E.sheafYoneda_essImage_closedUnderExtensions hS h₁ h₃ :
      E.sheafYoneda.essImage S.X₂)
