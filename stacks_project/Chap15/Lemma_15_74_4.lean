module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Functoriality

@[expose] public section

/-!
# Composition of derived internal-Hom objects

Lemma 15.74.4 (0A8J): composition of derived internal-Hom objects is the canonical
closed-monoidal composition transported through an explicit fixed-right derived tensor model.
The reusable owner is `CategoryTheory.DerivedCategory.InternalHom`.

@stack 0A8J
-/

/- Lemma 15.74.4 (0A8J): canonical derived internal-Hom composition and its functoriality. -/
@[stacks 0A8J "derived internal-Hom composition"]
#check @CategoryTheory.DerivedCategory.InternalHom.compOf

#check @CategoryTheory.DerivedCategory.InternalHom.mapOf
#check @CategoryTheory.DerivedCategory.InternalHom.tensorMapOf
#check @CategoryTheory.DerivedCategory.InternalHom.compOf_natural_target
#check @CategoryTheory.DerivedCategory.InternalHom.compOf_natural_source
#check @CategoryTheory.DerivedCategory.InternalHom.compOf_natural_middle

#print axioms CategoryTheory.DerivedCategory.InternalHom.compOf
