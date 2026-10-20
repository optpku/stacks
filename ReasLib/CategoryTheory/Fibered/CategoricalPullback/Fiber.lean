module

public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Fiber.Forward
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Fiber.Reverse
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Fiber.Equivalence
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Fiber.Chosen

/-!
# Fibers of categorical-pullback projections

Compatibility aggregate for the categorical-pullback fiber comparison API.
The canonical declarations are organized below
`CategoricalPullback.Fiber.{forward,reverse,equivalence,chosen}`: forward
strictification, the choice-free reverse embedding, unit/counit and
equivalence data, and the `IsFibered` specialization respectively. Focused
clients can import the corresponding leaf.

The compatibility path deliberately has no declarations of its own.
-/
