/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Closure
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Basic
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Graph
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Functoriality.Forget
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Functoriality.Map
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Functoriality.Coherence
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Pseudofunctor.Construction
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Pseudofunctor.Projections
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Symmetry.Swap
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Symmetry.Equivalence
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Bilimit
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.ObjectProperty.Equivalence
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.ObjectProperty.Change
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.ObjectProperty.Congruence
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.ObjectProperty.Postcompose
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.ObjectProperty.Projection
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Fibered.Closure
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Fibered.Pith

/-!
# Two-fibre products in locally induced bicategories

Explicit based pseudo-pullbacks lift to locally induced bicategories whenever the selected object
and hom properties are closed under, and detected by, the two projections. The closure class
itself accepts every universe-stable layer
`BasedCategory.{max v vB, max w (max u (max v vB))} C`; the apex, cone, graph, functoriality,
swap, and bilimit facades all live on that same general stable owner.

This compatibility aggregate re-exports the responsibility-specific leaves for existing callers.
-/
