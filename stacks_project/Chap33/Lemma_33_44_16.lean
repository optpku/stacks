module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Cohomology

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
universe u

/- Lemma 33.44.16 (1): a proper curve over an algebraically closed field has an
invertible module whose degree-zero cohomology has dimension one and whose degree-one
cohomology vanishes. -/
@[stacks 0B8Z] #check
  (AlgebraicGeometry.Scheme.Modules.exists_invertible_with_h0_finrank_one_h1_zero :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      (X : Over (Spec (CommRingCat.of k))) [Curve X] [IsProper X.hom],
      ∃ (ℒ : X.left.Modules) (hℒ : Scheme.Modules.Invertible ℒ),
        let _ : Scheme.Modules.Invertible ℒ := hℒ
        Scheme.Hom.cohomologyFinrank X.hom ℒ 0 = 1 ∧
          IsZero (Scheme.Modules.cohomology ℒ 1))

/- Lemma 33.44.16 (2): a proper curve over an algebraically closed field has an
invertible module whose degree-zero and degree-one cohomology both vanish. -/
@[stacks 0B8Z] #check
  (AlgebraicGeometry.Scheme.Modules.exists_invertible_with_h0_finrank_zero_h1_zero :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      (X : Over (Spec (CommRingCat.of k))) [Curve X] [IsProper X.hom],
      ∃ (𝒩 : X.left.Modules) (h𝒩 : Scheme.Modules.Invertible 𝒩),
        let _ : Scheme.Modules.Invertible 𝒩 := h𝒩
        Scheme.Hom.cohomologyFinrank X.hom 𝒩 0 = 0 ∧
          IsZero (Scheme.Modules.cohomology 𝒩 1))
