module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Derived.Cohomology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GroupoidsOver

universe u

/- Lemma 96.26.2: A quasi-coherent derived object with cohomology vanishing above
`b` has a quasi-coherent degree-`b` cohomology sheaf on the chaotic affine site. -/
@[stacks 0H0I] #check (AlgebraicGeometry.GroupoidsOver.cohomology_isQuasicoherent :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} (M : QC X) (b : ℤ),
    (∀ i : ℤ, b < i → IsZero (QC.cohomology M i)) →
      (QC.cohomology M b).IsQuasicoherent)
