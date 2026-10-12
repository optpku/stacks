/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ProEtale.Constructible
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open TopologicalSpace
open Topology

universe u w

namespace CategoryTheory.Sheaf

variable {X : Scheme.{u}}

/- Definition 61.27.1 -/
@[stacks 09AJ] #check (CategoryTheory.Sheaf.IsConstructibleProEtaleModule :
  ∀ {X : Scheme.{u}} {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ],
    (∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf (ProEt.topology X) (ModuleCat.{w} Λ) →
        Sheaf (ProEt.topology Y) (ModuleCat.{w} Λ)) →
    (∀ {Y : Scheme.{u}},
      Sheaf (ProEt.topology Y) (ModuleCat.{w} Λ) → Prop) →
    Sheaf (ProEt.topology X) (ModuleCat.{w} Λ) → Prop)

end CategoryTheory.Sheaf
