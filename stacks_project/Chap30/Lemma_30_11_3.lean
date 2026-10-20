module

import ReasLib.AlgebraicGeometry.Scheme.Module.SerreCondition.InternalHom
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalClosed

universe u

/- Lemma 30.11.3 (1): if `𝒢` satisfies `(S₁)`, then the internal Hom from `ℱ` to `𝒢` also
satisfies `(S₁)`. -/
@[stacks 0AXQ] #check
  (@AlgebraicGeometry.Scheme.Modules.satisfiesSerreConditionS_one_internalHom_of_satisfiesSerreConditionS_one :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      {ℱ 𝒢 : X.Modules} [ℱ.IsCoherent] [𝒢.IsCoherent],
      AlgebraicGeometry.Scheme.Modules.satisfiesSerreConditionS 𝒢 1 →
        AlgebraicGeometry.Scheme.Modules.satisfiesSerreConditionS ((ihom ℱ).obj 𝒢) 1)

/- Lemma 30.11.3 (2): if `𝒢` satisfies `(S₂)`, then the internal Hom from `ℱ` to `𝒢` also
satisfies `(S₂)`. -/
@[stacks 0AXQ] #check
  (@AlgebraicGeometry.Scheme.Modules.satisfiesSerreConditionS_two_internalHom_of_satisfiesSerreConditionS_two :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      {ℱ 𝒢 : X.Modules} [ℱ.IsCoherent] [𝒢.IsCoherent],
      AlgebraicGeometry.Scheme.Modules.satisfiesSerreConditionS 𝒢 2 →
        AlgebraicGeometry.Scheme.Modules.satisfiesSerreConditionS ((ihom ℱ).obj 𝒢) 2)
