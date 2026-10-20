/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Flattening.InDimensions.Representation
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Flattening
namespace flatInDimensionsFunctor

/- Lemma 38.27.4: if a finitely presented module admits a complete dévissage over `s`
and is flat in dimensions at least `d + 1`, then near `s` its degree-`d` flattening
functor is represented by a finitely presented monomorphism. -/
@[stacks 05UF] #check
  (AlgebraicGeometry.Scheme.Flattening.flatInDimensionsFunctor.existsMonomorphismRepresentationNear :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FinitePresentation f]
      (ℱ : X.Modules) [ℱ.IsFinitePresentation] (s : S) (d : ℕ),
      Nonempty (Modules.CompleteDevissageOver f ℱ s) →
        Modules.flatOverInDimensionsGE ℱ f (d + 1) →
          ∃ U : S.Opens, s ∈ U ∧
            ∃ Z : Over U.toScheme,
              Nonempty
                ((flatInDimensionsFunctor (pullback.snd f U.ι)
                  (Modules.baseChangeModule f U.ι ℱ) d).RepresentableBy Z) ∧
                Mono Z.hom ∧ Scheme.Hom.FinitePresentation Z.hom)

end flatInDimensionsFunctor
end Flattening
end Scheme
end AlgebraicGeometry
