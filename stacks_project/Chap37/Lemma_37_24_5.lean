/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.FiberClosure

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.24.5: the closures in the total space of a finite closed cover of the generic
fiber cover every fiber over some nonempty open subset of the irreducible base. -/
@[stacks 054Y] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.exists_open_fiberClosure_cover :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f] [IrreducibleSpace Y] {n : ℕ}
      (Zη : Fin n → TopologicalSpace.Closeds (f.fiber (genericPoint Y))),
      iSup Zη = ⊤ →
        ∃ V : Y.Opens, Nonempty V ∧ ∀ y : Y, y ∈ V →
          iSup (fun i ↦
            (TopologicalSpace.Closeds.closure
              ((f.fiberι (genericPoint Y)) ''
                (Zη i : Set (f.fiber (genericPoint Y))))).preimage
                  (f.fiberι y).continuous) = ⊤)

end AlgebraicGeometry.Scheme.Hom
