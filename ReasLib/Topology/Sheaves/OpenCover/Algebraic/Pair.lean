/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.OpenCover.Pair
public import ReasLib.Topology.Sheaves.OpenCover.Algebraic.Basis
import Mathlib.Tactic.CrossRefAttribute

/-!
# Algebraic sheaf gluing on a pair of opens

This module specializes the algebraic open-cover descent equivalence to the canonical
`Bool`-indexed cover associated to two opens.

@stack 05EV
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace
open TopologicalSpace.Opens

noncomputable section

universe u v

namespace TopCat.Sheaf.OpenCover.Gluing

variable {X : TopCat.{u}} {C : Type v} [Category.{u} C]

/-- Restriction to two opens covering the ambient space is an equivalence between algebraic
structure-valued sheaves and their open-cover gluing data. -/
@[stacks 05EV "algebraic sheaf gluing on two opens"]
theorem ofSheafFunctor_pair_isEquivalence
    {F : C ⥤ Type u} [IsAlgebraicStructure C F]
    (U V : Opens X) (hcover : U ⊔ V = ⊤) :
    Functor.IsEquivalence
      (ofSheafFunctor (C := C) (TopologicalSpace.OpenCover.pair U V)) := sorry

end TopCat.Sheaf.OpenCover.Gluing
