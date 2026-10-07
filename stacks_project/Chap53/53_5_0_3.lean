module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree.ChernClass

universe u

/- 53.5.0.3: For a proper scheme `X` of dimension at most one over a field and a finite
locally free module `E` of constant rank `n`, `χ(X, E)` is the Chow degree of
`c₁(E) ∩ [X]₁` plus `n χ(X, 𝒪_X)`. -/
@[stacks 0BRZ] #check
  (AlgebraicGeometry.Scheme.Modules.curveRiemannRoch :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.IsProper X.hom],
    (hdim : topologicalKrullDim X.left ≤ 1) →
    ∀ (E : X.left.Modules) (n : ℕ)
      [AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank n E],
      -- Local instance justification (defeq pin): the canonical properness-induced Noetherian structure aligns coherence inference for the Euler characteristics with curveDegree.
      let _ : AlgebraicGeometry.IsLocallyNoetherian X.left :=
        AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian X.hom
      AlgebraicGeometry.Scheme.Hom.eulerCharacteristic X.hom E =
        AlgebraicGeometry.ChowGroup.degree X
            (AlgebraicGeometry.Scheme.Modules.firstChernClassCapFundamental X E) +
          (n : ℤ) * AlgebraicGeometry.Scheme.Hom.eulerCharacteristic X.hom
            (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules))
