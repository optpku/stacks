module

public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.8.6
@stack 00D9
-/

universe u v

namespace CategoryTheory

section

variable {R : Type u} [Ring R]
variable {I : Type v} [Preorder I]
variable {M N : I ⥤ ModuleCat R}

/- Definition 10.8.6: a homomorphism of systems of `R`-modules over the same preordered set `I`
is exactly a natural transformation `M ⟶ N`, i.e. the specialization of Categories,
Definition 4.2.15 to the functor category from the preorder `I` to `ModuleCat R`. Its primitive
data are the component morphisms `Φ.app i : M.obj i ⟶ N.obj i`; compatibility with transition maps
is derived from naturality. -/
@[stacks 00D9 "system morphism as a natural transformation"]
#check (M ⟶ N)

/- The family of component module homomorphisms is the `app` field. -/
@[stacks 00D9 "component maps"]
#check @NatTrans.app

/- Compatibility with every transition map is the `naturality` field. -/
@[stacks 00D9 "transition-map compatibility"]
#check @NatTrans.naturality

end

end CategoryTheory
