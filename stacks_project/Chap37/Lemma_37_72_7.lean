/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.UniversalContractionNeighborhood
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 37.72.7: the special-fibre hypotheses for a proper commutative triangle
give one open neighbourhood of `Yₛ` on which target and source flatness, the
fibre-dimension bound, degree-one vanishing, and the structure-sheaf isomorphism
hold and remain true after every base change `S' ⟶ S`. -/
@[stacks 0E7L] #check
  (AlgebraicGeometry.Scheme.HigherDirectImage.exists_universalContractionNeighborhood :
    ∀ {X Y S : Scheme.{u}}
      (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y) (sq : CommSq f p q (𝟙 S)) (s : S)
      [LocallyOfFinitePresentation p]
      (hflat : ∀ xₛ : p.fiber s, p.flatAt (p.fiberι s xₛ))
      [LocallyOfFinitePresentation q] [IsProper f]
      (hdim : ∀ yₛ : q.fiber s,
        topologicalKrullDim
          ((Scheme.Hom.fiberMap p f (𝟙 S) q sq s).fiber yₛ) ≤ (1 : WithBot ℕ∞))
      (hH1 : IsZero
        (RingedSpace.Hom.higherDirectImageModule
          (Scheme.Hom.fiberMap p f (𝟙 S) q sq s).toShHom
          (SheafOfModules.unit (p.fiber s).ringCatSheaf) 1))
      [IsIso (RingedSpace.Hom.commRingSheafPushforwardMap
        (Scheme.Hom.fiberMap p f (𝟙 S) q sq s).toShHom)],
      Nonempty
        (AlgebraicGeometry.Scheme.HigherDirectImage.UniversalContractionNeighborhood
          p q f s))
