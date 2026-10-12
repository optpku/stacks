/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Definition
import StacksCheckRecall

open CategoryTheory.Action.ModuleCat

universe u v

variable (R : Type u) [Ring R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/- Definition 59.57.1 (1): the category of discrete continuous `G`-modules,
represented canonically by `DiscreteModuleCat ℤ G`; its morphisms are equivariant
homomorphisms inherited from `Action.Hom`. -/
@[stacks 04JP] #check (CategoryTheory.Action.ModuleCat.DiscreteModuleCat ℤ G : Type (v + 1))

/- Definition 59.57.1 (2): the category of discrete continuous `R`-modules with
`G`-action, represented canonically by `DiscreteModuleCat R G`; its morphisms are
equivariant `R`-linear maps inherited from `Action.Hom`. -/
@[stacks 04JP] #check (CategoryTheory.Action.ModuleCat.DiscreteModuleCat R G : Type (max u v + 1))
