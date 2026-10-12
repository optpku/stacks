/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap48.Definition_48_28_1_RelativeDualizingComplex

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeDualizingComplex

/- Lemma 48.28.5 -/
@[stacks 0E2X] #check (AlgebraicGeometry.Scheme.RelativeDualizingComplex.existsRelativeDualizingComplex :
  {X S : Scheme.{u}} → (f : X ⟶ S) → [Flat f] → [LocallyOfFinitePresentation f] →
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)] →
    ∃ (W : (pullback f f).Opens) (δ : X ⟶ W.toScheme)
      (h_closed : IsClosedImmersion δ)
      (hδ : δ ≫ W.ι = pullback.diagonal f)
      (monoidalW : MonoidalCategory
        (RingedSpace.ModuleDerived W.toScheme.toRingedSpace))
      (laxPushforward : @CategoryTheory.Functor.LaxMonoidal
        (RingedSpace.ModuleDerived X.toRingedSpace) inferInstance inferInstance
        (RingedSpace.ModuleDerived W.toScheme.toRingedSpace) inferInstance monoidalW
        (RingedSpace.moduleDerivedPushforward δ.toShHom))
      (H : @MonoidalClosed (RingedSpace.ModuleDerived W.toScheme.toRingedSpace)
        inferInstance monoidalW),
      Nonempty (@Scheme.RelativeDualizingComplex X S f inferInstance inferInstance W δ
        h_closed hδ inferInstance monoidalW laxPushforward H))

end AlgebraicGeometry.Scheme.RelativeDualizingComplex
