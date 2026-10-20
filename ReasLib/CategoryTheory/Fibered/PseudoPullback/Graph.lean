module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Graph.Construction
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Graph.Counit
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Graph.Unit
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Graph.Equivalence

/-!
# The graph into an identity pseudo-pullback

For a based functor `F : X ⥤ᵇ Y`, its graph is the canonical based functor

`X ⥤ᵇ BasedCategory.PseudoPullback F (𝟭 Y)`

sending `x` to `(x, F.obj x, 𝟙 (F.obj x))`.  It is an equivalence, its first projection is the
identity, and its second projection is `F`.

This is the compatibility import for the graph construction.  The implementation is organized by
mathematical layer:

* Construction: graph construction and its object, morphism, and projection computations;
* Counit: the explicit retraction-to-identity component and based natural isomorphism;
* Unit: the identity-to-graph-retraction based natural isomorphism;
* Equivalence: quasi-inverse data, stable-universe bicategorical equivalence, and the
  `BasedFunctor.IsEquivalence` instance. Supporting declarations are organized under their
  lowercase `graph` owner.

New developments should import the smallest leaf that supplies their required API. This aggregate
remains the stable broad entry point for existing users.
-/
