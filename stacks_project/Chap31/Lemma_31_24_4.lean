module

import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.MeromorphicSection
import StacksCheckRecall

universe u

/- Lemma 31.24.4: A locally Noetherian scheme without embedded points admits a regular
meromorphic section of every invertible module. -/
@[stacks 0EMI] #check
  (AlgebraicGeometry.exists_regularMeromorphicSection_of_isLocallyNoetherian_noEmbeddedPoints :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
      (_ : X.embeddedPoints = (∅ : Set X))
      (ℒ : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible ℒ],
      ∃ s : X.toLocallyRingedSpace.meromorphicSections ℒ,
        X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s)
