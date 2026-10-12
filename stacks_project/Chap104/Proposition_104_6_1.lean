/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap104.Proposition_104_6_1_Plus
public import stacks_project.Chap104.Proposition_104_6_1_Pushforward
import StacksCheckRecall

/-!
# Proposition 104.6.1

A quasi-compact quasi-separated morphism of algebraic stacks has a derived
direct image inducing a commutative diagram on `D⁺_{Parasitic ∩ LQCoh^{fbc}}`,
`D⁺_{LQCoh^{fbc}}`, and unbounded `D(𝒪)`, hence a functor
`Rf_{QCoh,*} : D⁺_QCoh(𝒪_X) ⥤ D⁺_QCoh(𝒪_Y)`. The higher direct images
`R^i f_QCoh` of Proposition 103.11.1 agree with `H^i ∘ Rf_{QCoh,*}` after
placing a quasi-coherent module in degree zero.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
variable [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]

/- Proposition 104.6.1 (1): let `f : X ⟶ Y` be a quasi-compact and
quasi-separated morphism of algebraic stacks. The functor `Rf_*` induces a
commutative diagram relating `D⁺_{Parasitic ∩ LQCoh^{fbc}}`,
`D⁺_{LQCoh^{fbc}}`, and unbounded `D(𝒪)`, with vertical arrows the local
unbounded derived pushforward, via the canonical squares
`derivedPushforwardPlusParasitic f ⋙ derivedParasiticLQCohFbcPlus.inclusion Y ≅
derivedParasiticLQCohFbcPlus.inclusion X ⋙ derivedPushforwardPlusLQCohFbc f`
and
`derivedPushforwardPlusLQCohFbc f ⋙ DerivedLQCohFbc.Plus.ambient Y ≅
DerivedLQCohFbc.Plus.ambient X ⋙ fppfModuleDerivedPushforward f`. -/
@[stacks 07BC]
#check (derivedPushforwardPlusParasitic_comp_inclusion f)
@[stacks 07BC]
#check (derivedPushforwardPlusLQCohFbc_comp_ambient f)

/- Proposition 104.6.1 (2): the commutative diagram therefore induces a
functor `Rf_{QCoh,*} : D⁺_QCoh(𝒪_X) ⥤ D⁺_QCoh(𝒪_Y)` on quotient
categories. -/
@[stacks 07BC]
#check (DerivedQCoh.pushforward f)

/- Proposition 104.6.1 (3): the functors `R^i f_QCoh` of Proposition 103.11.1
agree with `H^i ∘ Rf_{QCoh,*}` for `H^i` as in 104.5.1.1, after placing a
quasi-coherent module in degree zero, via the specified isomorphism
`singlePlus X ⋙ pushforward f ⋙ Plus.inclusion Y ⋙ homologyFunctor Y (i : ℤ) ≅
QCoh.higherDirectImageFunctor f i ⋙ QCoh.toFppfQuotient Y`. -/
@[stacks 07BC]
#check (DerivedQCoh.homology_pushforward_single_iso f)

end AlgebraicGeometry.AlgebraicStack
