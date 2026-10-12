/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.TorAmplitude.FinitePresentationDescent

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 37.54.3 (Longke Tang): for a surjective finite-presentation morphism
`f : X ⟶ S` and a nonpositive `M : DerivedQCoh S`, the underlying derived module
of `M` has a flat representative concentrated in degree zero exactly when the same holds after
derived pullback. -/
@[stacks 0H89] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.hasFlatRepresentativeIn_zero_iff_pullback :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Surjective f] [Scheme.Hom.FinitePresentation f]
      (M : DerivedQCoh S) (hM : ((inclusion S).obj M).IsLE 0),
      RingedSpace.ModuleDerived.HasFlatRepresentativeIn ((inclusion S).obj M) 0 0 ↔
        RingedSpace.ModuleDerived.HasFlatRepresentativeIn
          ((inclusion X).obj ((pullback f).obj M)) 0 0)

end AlgebraicGeometry.Scheme.DerivedQCoh
