module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.MeromorphicSection
import StacksCheckRecall

/-!
# Lemma 31.25.4

Existence of regular meromorphic sections of invertible modules.

@stack 02OZ
-/

@[expose] public section

universe u

/- Lemma 31.25.4: Existence of regular meromorphic sections of invertible modules. -/
@[stacks 02OZ] #check
  (AlgebraicGeometry.exists_regularMeromorphicSection_of_isIntegral :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
      (ℒ : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible ℒ],
      ∃ s : X.toLocallyRingedSpace.meromorphicSections ℒ,
        X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s)

#check
  (AlgebraicGeometry.Scheme.Modules.Invertible.exists_regularMeromorphicSection_of_isReduced :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsReduced X]
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
      (ℒ : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible ℒ],
      ∃ s : X.toLocallyRingedSpace.meromorphicSections ℒ,
        X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s)

#check
  (AlgebraicGeometry.exists_regularMeromorphicSection_of_isLocallyNoetherian_noEmbeddedPoints :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
      (_ : X.embeddedPoints = (∅ : Set X))
      (ℒ : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible ℒ],
      ∃ s : X.toLocallyRingedSpace.meromorphicSections ℒ,
        X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s)
