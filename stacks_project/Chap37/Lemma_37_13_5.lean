module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallySmooth.NaiveCotangent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FormallySmooth

/- Lemma 37.13.5: a scheme morphism is formally smooth exactly when its degree `-1`
naive-cotangent homology is zero and its relative differentials are locally projective. -/
@[stacks 0D0L] #check
  (AlgebraicGeometry.FormallySmooth.iff_naiveCotangent :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      FormallySmooth f ↔
        IsZero ((NL[f.toShHom]).homology (-1)) ∧
          Scheme.Modules.IsLocallyProjective Ω[f.toShHom])

end AlgebraicGeometry.FormallySmooth
