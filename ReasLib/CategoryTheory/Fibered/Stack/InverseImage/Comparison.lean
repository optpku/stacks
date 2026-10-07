module

public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Comparison.Pullback
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Comparison.Cartesian.MapHom
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Comparison.MapHom.Comparison
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.Stack.Over.Equivalence
public import ReasLib.CategoryTheory.Fibered.Stack.Over.Local

/-!
# Comparisons and pseudofunctoriality for inverse-image stacks

This aggregate exposes the canonical pullback comparison, the two explicit constructions of the
inverse-image functor on morphism categories, the natural isomorphism comparing them, and the
explicit-choice pseudofunctor package.

The two Hom constructions are intentionally not aliases: `Comparison/Cartesian/MapHom` is the
heterogeneous canonical/explicit route, while `Comparison/MapHom/Direct` and
`Comparison/MapHom/OfHomQuasiInverse` serve callers who already own fixed-owner inversion or a
Hom quasi-inverse.  The aggregate is an import convenience; focused consumers should choose the
leaf matching the data they already have.
-/
