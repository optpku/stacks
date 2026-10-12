/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ProjectionFormula.RelativeExtRepresentability

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalClosed
open RingedSpace.Module.Derived RingedSpace.ModuleDerived

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.ProjectionFormula

/- Remark 36.35.12 (1): under the hypotheses of Lemma 36.35.11, the relative Ext
functor of `K` against `E ⊗ Lf^*(-)` has a pseudo-coherent representative on `S`. -/
@[stacks 0DJV] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.ProjectionFormula.existsPseudoCoherentRelativeExtRepresentation :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [CompactSpace S] [QuasiSeparatedSpace S]
      [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
      [KFlat.HomotopyTensorDescends X.toRingedSpace]
      [KFlat.TensorDescends X.toRingedSpace]
      [KFlat.IsLocalization X.toRingedSpace]
      [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
      [KFlat.HomotopyTensorDescends S.toRingedSpace]
      [KFlat.TensorDescends S.toRingedSpace]
      [KFlat.IsLocalization S.toRingedSpace]
      [MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)]
      (E K : RingedSpace.ModuleDerived X.toRingedSpace)
      (_ : IsPerfectRelativeTo f E)
      (_ : RingedSpace.ModuleDerived.IsPseudoCoherent K),
      ∃ L : RingedSpace.ModuleDerived S.toRingedSpace,
        RingedSpace.ModuleDerived.IsPseudoCoherent L ∧
          RepresentsRelativeExt f K E L)

/- Remark 36.35.12 (2): any two pseudo-coherent representatives of the relative Ext
functor furnished by Lemma 36.35.11 are isomorphic in the derived category of `S`. -/
@[stacks 0DJV] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.ProjectionFormula.relativeExtRepresentation_unique :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [CompactSpace S] [QuasiSeparatedSpace S]
      [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
      [KFlat.HomotopyTensorDescends X.toRingedSpace]
      [KFlat.TensorDescends X.toRingedSpace]
      [KFlat.IsLocalization X.toRingedSpace]
      [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
      [KFlat.HomotopyTensorDescends S.toRingedSpace]
      [KFlat.TensorDescends S.toRingedSpace]
      [KFlat.IsLocalization S.toRingedSpace]
      [MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)]
      (E K : RingedSpace.ModuleDerived X.toRingedSpace)
      (_ : IsPerfectRelativeTo f E)
      (_ : RingedSpace.ModuleDerived.IsPseudoCoherent K)
      (L L' : RingedSpace.ModuleDerived S.toRingedSpace)
      (_ : RingedSpace.ModuleDerived.IsPseudoCoherent L)
      (_ : RingedSpace.ModuleDerived.IsPseudoCoherent L')
      (_ : RepresentsRelativeExt f K E L)
      (_ : RepresentsRelativeExt f K E L'),
      IsIsomorphic L L')

end AlgebraicGeometry.Scheme.ModuleDerived.ProjectionFormula
