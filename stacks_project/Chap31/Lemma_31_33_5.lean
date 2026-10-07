module

import ReasLib.AlgebraicGeometry.Scheme.StrictTransform.EffectiveCartier
import StacksCheckRecall

universe u

/- Lemma 31.33.5 (1)

Let `S` be a scheme, `I` an ideal sheaf on `S`, and `D` an effective Cartier divisor on
`S`. If `b : S' ⟶ S` is the blowup in `I`, then it is also the blowup in `I * D`.
-/
@[stacks 080H] #check
  (AlgebraicGeometry.IsBlowup.mul_effectiveCartier :
    ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
      (I D : S.IdealSheafData)
      [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
      (b : S' ⟶ S) [AlgebraicGeometry.IsBlowup b I],
      AlgebraicGeometry.IsBlowup b (I * D))

/- Lemma 31.33.5 (2)

With the same notation, let `f : X ⟶ S` and let `ℱ` be a quasicoherent `O_X`-module.
If every local section of `ℱ` supported on the inverse image of `D` is zero, then its strict
transforms relative to the centers `I` and `I * D` agree.
-/
@[stacks 080H] #check
  (AlgebraicGeometry.Scheme.Modules.strictTransformModule_mul_eq_of_noSectionsSupportedOn :
    ∀ {S S' X : AlgebraicGeometry.Scheme.{u}}
      (I D : S.IdealSheafData)
      [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
      (b : S' ⟶ S) [AlgebraicGeometry.IsBlowup b I]
      (f : X ⟶ S) (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      (∀ (U : X.Opens) (s : ℱ.val.obj (Opposite.op U)),
        SheafOfModules.localSectionSupport s ⊆
          {x : U | (x : X) ∈ ((D.comap f).support : Set X)} → s = 0) →
        AlgebraicGeometry.strictTransformModule b (I.comap b) f ℱ =
          AlgebraicGeometry.strictTransformModule b ((I * D).comap b) f ℱ)
