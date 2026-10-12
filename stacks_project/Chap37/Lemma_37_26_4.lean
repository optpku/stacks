/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.GeometricallyReducedFiber
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.26.4: if a finite-type morphism to an irreducible scheme has geometrically
reduced generic fibre, then its restriction over some nonempty open subscheme has
geometrically reduced fibres. -/
@[stacks 0578] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.exists_open_geometricallyReduced :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f] [IrreducibleSpace Y]
      [GeometricallyReduced (f.fiberToSpecResidueField (genericPoint Y))],
      ∃ V : Y.Opens, Nonempty V ∧ GeometricallyReduced (f ∣_ V))

end AlgebraicGeometry.Scheme.Hom
