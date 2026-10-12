/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.GeometricallyConnectedFiber

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.FinitePresentation

/- Lemma 37.46.1: a flat finitely presented morphism with geometrically reduced fibres and a
finite locally free multisection meeting a geometrically connected fibre admits a quasi-compact
source open containing that fibre whose nonempty fibres are geometrically connected. -/
@[stacks 057I]
#check
  (AlgebraicGeometry.Scheme.Hom.FinitePresentation.exists_compactOpen_geometricallyConnectedFibers :
    ∀ {Z X Y : Scheme.{u}} (σ : Z ⟶ X) (f : X ⟶ Y) (y : Y)
      [FinitePresentation f] [Flat f] [IsFiniteLocallyFree (σ ≫ f)]
      (_ : Nonempty ((σ ≫ f).fiber y)) [GeometricallyReduced f]
      [GeometricallyConnected (f.fiberToSpecResidueField y)],
      ∃ U : X.Opens, IsCompact (U : Set X) ∧ f ⁻¹' {y} ⊆ U ∧
        ∀ y' : Y, Nonempty ((U.ι ≫ f).fiber y') →
          GeometricallyConnected ((U.ι ≫ f).fiberToSpecResidueField y'))

end AlgebraicGeometry.Scheme.Hom.FinitePresentation
