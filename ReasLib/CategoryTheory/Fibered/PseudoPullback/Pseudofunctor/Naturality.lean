module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Pseudofunctor.Computations.Naturality

/-!
# Naturality for the explicit pseudo-pullback pseudofunctor

This aggregate routes the focused naturality leaf for the bundled pseudofunctor's action on cospan
`2`-cells. The declarations are owned by `Computations.Naturality`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open BasedNatIso
open Functor.IsHomLift
open Functor.Fiber
open CategoricalPullback
open scoped CategoricalPullback
open scoped Bicategory BasedFunctor Pseudofunctor.StrongTrans

universe u v w vB
