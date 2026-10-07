module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.FittingIdeal

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry RelativeDerivation

universe u

/- Remark 111.50.2 (1): the `k`th Fitting ideal of `Ω[f.toShHom]` is
`Scheme.fittingIdealSheaf (Ω[f.toShHom]) k`. Its closed subscheme `.subscheme`
with inclusion `.subschemeι` is the usual candidate for the singular scheme of
`f : X ⟶ S` when the relative dimension is `k`. Parts (a) and (b) of the
preceding exercise show this can fail without constant fibre dimension. -/
@[stacks 02FD] #check
  (AlgebraicGeometry.Scheme.Hom.fittingIdealSheaf_differentials_support_eq_compl_smoothLocus :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ) [Flat f] [LocallyOfFinitePresentation f]
      [Scheme.Hom.RelativeDimension f d],
      ((Scheme.fittingIdealSheaf (Ω[f.toShHom]) d).support : Set X) =
        (f.smoothLocus : Set X)ᶜ)

/- Remark 111.50.2 (2): in good families of curves, such as a syntomic morphism
of relative dimension one, the `0`th Fitting ideal of `Ω[f.toShHom]` is the
zero ideal sheaf. The first Fitting ideal then has the expected singular
support in this formal good case, while the scheme-theoretic singular locus
is the Fitting closed subscheme, not merely the reduced induced structure on
that support. Flatness alone is not enough, as in part (b). -/
@[stacks 02FD] #check
  (AlgebraicGeometry.Scheme.Hom.fittingIdealSheaf_differentials_zero_eq_bot :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.SyntomicOfRelativeDimension f 1],
      Scheme.fittingIdealSheaf (Ω[f.toShHom]) 0 = ⊥)

/- Remark 111.50.2 (3): under the same syntomic relative-dimension-one
hypothesis, the support of the `1`st Fitting ideal is the complement of the
smooth locus. This identifies the support only; the chosen scheme structure is
still the closed subscheme associated to `Scheme.fittingIdealSheaf
(Ω[f.toShHom]) 1`, with its inclusion `.subschemeι`. Syntomic relative curves
give a sufficient formal good case, not a definition of every good case. -/
@[stacks 02FD] #check
  (AlgebraicGeometry.Scheme.Hom.fittingIdealSheaf_differentials_one_support_eq_compl_smoothLocus :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.SyntomicOfRelativeDimension f 1],
      ((Scheme.fittingIdealSheaf (Ω[f.toShHom]) 1).support : Set X) =
        (f.smoothLocus : Set X)ᶜ)
