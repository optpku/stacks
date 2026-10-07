module

-- Compatibility import: this was historically a public dependency of the monolithic file, and
-- retains its equivalence layer for clients that reached it through this entry point.
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Comparison
public import ReasLib.CategoryTheory.Fibered.Groupoids.BaseProjection.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.Comparison.Map
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.Comparison.Map.NatTrans
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.Comparison.Target
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.Comparison.Iso

/-!
# Square comparisons for relative representability

Compatibility aggregate for the comparison infrastructure between canonical two-fibre products
over the universe-closed identity fibration and ordinary categorical pullbacks over the original
base.

New developments should import the narrow leaf matching their use:

* `Fibered.Groupoids.BaseProjection.PseudoPullback` for the transport from the universe-closed
  base;
* `Comparison.Map` for a morphism into the canonical two-fibre product;
* `Comparison.Map.NatTrans` for the local hom functor, its `2`-cell action, and induced
  isomorphisms between comparison maps;
* `Comparison.Target` for a pseudo-pullback cone;
* `Comparison.Iso` for the assembled natural comparison isomorphism.
-/
