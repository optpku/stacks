module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.DividedPower
import StacksCheckRecall
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KaehlerDifferential.DeRham
open DividedPowerScheme.RelativeDifferentials
open scoped AlgebraicGeometry RelativeDerivation

universe u

/- Lemma 60.12.2 (1): the divided-power differential quotient is a quasi-coherent
`𝒪_T`-module. -/
@[stacks 07IY] #check
  (DividedPowerScheme.RelativeDifferentials.module_isQuasicoherent :
    ∀ (T : DividedPowerScheme.{u}) (S : Scheme.{u}) (f : T.scheme ⟶ S)
      (D : DividedPowerScheme.RelativeDifferentials T S f),
      D.module.IsQuasicoherent)

/- Lemma 60.12.2 (2): on affine opens `W ⊆ T` mapping into `V ⊆ S`, the sections of the
divided-power differential quotient are canonically identified with the ring-level module
`dividedPowerDifferential` of the induced map on section rings. -/
@[stacks 07IY] #check
  (DividedPowerScheme.RelativeDifferentials.existsUnique_affineSectionsLinearEquiv :
    ∀ (T : DividedPowerScheme.{u}) (S : Scheme.{u}) (f : T.scheme ⟶ S)
      (D : DividedPowerScheme.RelativeDifferentials T S f)
      (W : T.scheme.affineOpens) (V : S.affineOpens)
      (hWV : W.1 ≤ f ⁻¹ᵁ V.1),
      ∃! eΩ : Γ(D.module, W.1) ≃ₗ[Γ(T.scheme, W.1)]
        dividedPowerDifferential
          (f.appLE V.1 W.1 hWV).hom (T.dividedPowers W),
        ∀ a : Γ(T.scheme, W.1),
          eΩ (quotientApp D W.1 (((d[f.toShHom]).app (op W.1)).d a)) =
            dividedPowerDifferentialDerivation
              (f.appLE V.1 W.1 hWV).hom (T.dividedPowers W) a)
