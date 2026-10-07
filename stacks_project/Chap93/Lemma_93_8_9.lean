module

public import stacks_project.Chap93.Lemma_93_8_9_Functor
import StacksCheckRecall

/-!
# Strict henselization of deformations of rings
-/

@[expose] public section

/- Lemma 93.8.9
In Example 93.8.1 let P be a k-algebra. Assume P is a local ring and let Psh
be a strict henselization of P. There is a natural functor of deformation
categories Def_P ⥤ Def_{Psh}. -/
@[stacks 0DYU]
#check @FlatAlgebraCat.strictHenselizationFunctor
