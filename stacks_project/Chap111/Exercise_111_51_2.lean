module

import ReasLib.AlgebraicGeometry.AffineScheme.IntegerPlane
import ReasLib.AlgebraicGeometry.Scheme.Module.BasicOpenTorsion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.AffinePlaneInt

/- Exercise 111.51.2 (1): if `F` is a quasi-coherent module on `affinePlaneInt` whose
restriction to the standard affine open `affinePlaneInt.basicOpen coordX` is zero, then every
global section `s` of `F` is killed by some power of `coordX`. -/
@[stacks 02FH]
 #check
  (AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_zero_of_isZero_restrict :
    ∀ {R : CommRingCat} (M : (Spec R).Modules) [M.IsQuasicoherent]
      (f : Γ(Spec R, ⊤)),
      IsZero (M.restrict ((Spec R).basicOpen f).ι) →
        ∀ s : Γ(M, ⊤), ∃ n : ℕ, f ^ n • s = 0)

/- Exercise 111.51.2 (2): without quasi-coherence, vanishing of the restriction to
`affinePlaneInt.basicOpen coordX` does not force every global section to be killed by a power
of `coordX`. -/
@[stacks 02FH]
 #check
  (AlgebraicGeometry.AffinePlaneInt.exists_section_not_pow_smul_eq_zero_of_isZero_restrict :
    ∃ (F : affinePlaneInt.Modules) (s : Γ(F, ⊤)),
      IsZero (F.restrict (affinePlaneInt.basicOpen coordX).ι) ∧
        ∀ n : ℕ, coordX ^ n • s ≠ 0)

end AlgebraicGeometry.AffinePlaneInt
