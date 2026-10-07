module

import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Order.Defs.PartialOrder
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.8.7

@stack 00DA
-/

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory

section

variable {R : Type u} [Ring R]
variable {I : Type v} [Preorder I]
variable {M N : I ⥤ ModuleCat R} [HasColimit M] [HasColimit N]
variable (Φ : M ⟶ N)

/- Lemma 10.8.7 is a `bridge/view` item in the colimit-of-module-systems domain: a morphism of
systems `Φ : M ⟶ N` over the same preordered set induces the canonical morphism on direct limits.
The owner abstraction is the colimit functor, so the source-facing specialization is the induced
map `colim.map Φ`, while the Chapter 4 theorem supplies its universal-property characterization. -/
@[stacks 00DA "induced colimit morphism"]
#check (colim.map Φ : colimit M ⟶ colimit N)

/- Lemma 10.8.7 (uniqueness): the chosen colimit map is characterized by its stage maps. -/
@[stacks 00DA "stage compatibility of the induced colimit morphism"]
#check @colimit.ι_map

@[stacks 00DA "uniqueness from the stage maps"]
#check @colimit.hom_ext

@[stacks 00DA "colimit universal-property owner"]
#check @colimit.isColimit

end

end CategoryTheory
