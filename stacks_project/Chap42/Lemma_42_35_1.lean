/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.BivariantClass.Descent

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

/- Lemma 42.35.1: a cycle-level cap family compatible with trivial-restriction
effective-Cartier Gysin pullback kills rational-equivalence boundaries. -/
@[stacks 0B7A] #check (AlgebraicGeometry.BivariantClass.boundaries_le_ker :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {f : X ⟶ Y} {p : ℤ}
    (cap : AlgebraicGeometry.BivariantClass.CycleCapFamily delta f p)
    (hcap : AlgebraicGeometry.BivariantClass.CompatibleWithTrivialCartierGysin delta cap)
    {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left) (k : ℤ),
    @RationalEquivalence.boundaries Y'.left
        (LocallyOfFiniteType.isLocallyNoetherian Y'.hom)
        (Y'.hom.relativeDimensionFunction delta) inferInstance k ≤
      (cap i f' g square k).ker)
