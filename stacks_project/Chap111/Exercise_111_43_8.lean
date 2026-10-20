module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.IdealComplement.Torsion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.IdealComplement

/- Exercise 111.43.8: for a ring `A`, a finite family `f : Fin t → A` generating an
ideal `I`, the open `U` complementary to `V(I)` in `Spec A`, a quasi-coherent module
`F` on `Spec A`, and a class `ξ` in `H^p(U, F)` with `p > 0`, there exists `n > 0`
such that `(f i) ^ n • ξ = 0` for every `i`. -/
@[stacks 0DAR] #check
  (AlgebraicGeometry.Scheme.Modules.IdealComplement.exists_pow_smul_eq_zero :
    ∀ {A : Type u} [CommRing A] {t : ℕ}
      (f : Fin t → A) (F : (Spec (CommRingCat.of A)).Modules) [F.IsQuasicoherent]
      {p : ℕ} (hp : 0 < p)
      (ξ : cohomology (Ideal.span (Set.range f))
        (F.restrict (idealComplementOpens (Ideal.span (Set.range f))).ι) p),
      ∃ n : ℕ, 0 < n ∧ ∀ i : Fin t, (f i) ^ n • ξ = 0)

end AlgebraicGeometry.Scheme.Modules.IdealComplement
