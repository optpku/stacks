module

public import ReasLib.Algebra.Category.ModuleCat.Tor.Product
import StacksCheckRecall

/-!
# Lemma 15.63.1: functoriality of products on Tor

@stack 068K

The Tor product, its unit, and the first-variable functoriality statements are owned by the shared
Tor API.
-/

@[expose] public section

/- Lemma 15.63.1 (Stacks `068K`): an algebra map in the first variable induces a product- and
unit-preserving map on graded Tor. -/
@[stacks 068K "first-variable Tor map preserves products"]
#check @CategoryTheory.ModuleCat.Tor.Product.map_mul

@[stacks 068K "first-variable Tor map preserves the unit"]
#check @CategoryTheory.ModuleCat.Tor.Product.map_unit

@[stacks 068K "first-variable Tor map is linear over the second algebra"]
#check @CategoryTheory.ModuleCat.Tor.Product.map_scalar

@[stacks 068K "first-variable Tor map preserves product and unit"]
#check @CategoryTheory.ModuleCat.Tor.Product.map_preserves_mul_and_unit

@[stacks 068K "canonical Tor product"]
#check @CategoryTheory.ModuleCat.Tor.Product.mul

@[stacks 068K "canonical Tor unit"]
#check @CategoryTheory.ModuleCat.Tor.Product.unit

end
