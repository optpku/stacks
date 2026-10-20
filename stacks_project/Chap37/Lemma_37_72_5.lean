/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.ContractionNeighborhood
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 37.72.5: the special-fibre hypotheses for a proper morphism in a
commutative triangle give one open neighbourhood of `Yₛ` on which flatness,
dimension at most one, degree-one vanishing, and structure-sheaf surjectivity
hold, with the latter three properties preserved by arbitrary base change. -/
@[stacks 0E7J] #check
  (AlgebraicGeometry.Scheme.HigherDirectImage.exists_contractionNeighborhood :
    ∀ {X Y S : Scheme.{u}}
      (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y) (sq : CommSq f p q (𝟙 S)) (s : S)
      [LocallyOfFinitePresentation p]
      (hflat : ∀ xₛ : p.fiber s, p.flatAt (p.fiberι s xₛ)) [IsProper f]
      (hdim : ∀ yₛ : q.fiber s,
        topologicalKrullDim
          ((Scheme.Hom.fiberMap p f (𝟙 S) q sq s).fiber yₛ) ≤ (1 : WithBot ℕ∞))
      (hH1 : IsZero
        (RingedSpace.Hom.higherDirectImageModule
          (Scheme.Hom.fiberMap p f (𝟙 S) q sq s).toShHom
          (SheafOfModules.unit (p.fiber s).ringCatSheaf) 1))
      [Sheaf.IsLocallySurjective
        (RingedSpace.Hom.commRingSheafPushforwardMap
          (Scheme.Hom.fiberMap p f (𝟙 S) q sq s).toShHom)],
      Nonempty
        (AlgebraicGeometry.Scheme.HigherDirectImage.ContractionNeighborhood p q f s))
