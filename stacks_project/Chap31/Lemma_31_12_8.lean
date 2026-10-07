module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.InternalHom
import StacksCheckRecall

/-!
# Lemma 31.12.8

Internal Hom from a coherent module preserves reflexivity.

@stack 0AY4
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 31.12.8: internal Hom from a coherent module to a coherent reflexive module is
reflexive. -/
@[stacks 0AY4] #check
  (AlgebraicGeometry.Scheme.Modules.isReflexive_internalHom :
    ∀ {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
      (ℱ 𝒢 : X.Modules) [ℱ.IsCoherent] [𝒢.IsCoherent],
      IsReflexive 𝒢 →
        IsReflexive (AlgebraicGeometry.Scheme.Modules.internalHom ℱ 𝒢))

end AlgebraicGeometry.Scheme.Modules
