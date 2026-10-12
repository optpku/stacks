/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Properties
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
import Mathlib.Tactic.CrossRefAttribute
import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.GenericFiber

/-!
# Closures of generic-fiber covers

This file relates finite closed covers of a generic fiber to the fibers over a nonempty open
subscheme of an irreducible target.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.FiniteType

/-- For a finite-type morphism to an irreducible scheme, the closures in the total space of a
finite closed cover of the generic fiber cover every fiber over some nonempty open subset of the
base. -/
@[stacks 054Y]
theorem exists_open_fiberClosure_cover
    {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f] [IrreducibleSpace Y] {n : ℕ}
    (Zη : Fin n → TopologicalSpace.Closeds (f.fiber (genericPoint Y)))
    (hcover : iSup Zη = ⊤) :
    ∃ V : Y.Opens, Nonempty V ∧ ∀ y : Y, y ∈ V →
      iSup (fun i ↦
        (TopologicalSpace.Closeds.closure
          ((f.fiberι (genericPoint Y)) '' (Zη i : Set (f.fiber (genericPoint Y))))).preimage
            (f.fiberι y).continuous) = ⊤ := sorry

end AlgebraicGeometry.Scheme.Hom.FiniteType
