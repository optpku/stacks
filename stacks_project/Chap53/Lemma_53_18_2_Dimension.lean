/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.Dimension
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Normalization.Dimension
public import ReasLib.AlgebraicGeometry.Scheme.Reduction.Dimension

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

#check (AlgebraicGeometry.Scheme.topologicalKrullDim_reduction :
  ∀ (X : Scheme.{u}), topologicalKrullDim X.reduction = topologicalKrullDim X)

#check (AlgebraicGeometry.Scheme.isClosedImmersion_reductionι :
  ∀ (X : Scheme.{u}), IsClosedImmersion (Scheme.reductionι X))

#check (AlgebraicGeometry.Scheme.Hom.ProperBirational.topologicalKrullDim_le_one :
  ∀ (k : Type u) [Field k] {X X' : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p]
    (f : X' ⟶ X) (hdim : topologicalKrullDim X ≤ 1) [IsProper f] [IsBirational f],
    topologicalKrullDim X' ≤ 1)

#check (AlgebraicGeometry.SchemeOverField.Normalization.topologicalKrullDim_eq :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [LocallyOfFiniteType X.hom],
    topologicalKrullDim (SchemeOverField.normalization X).left =
      topologicalKrullDim X.left)
