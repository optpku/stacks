module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap71.Lemma_71_4_4_RelativeWeakAss

/-!
# Lemma 71.4.4

Weak association of a quasi-coherent module to a point of the source of a
morphism of algebraic spaces is independent of étale scheme charts of the
target and of étale charts of the fibre product, and equivalent to existence
of a field-valued fibre lift. A monomorphic field-valued representative, when
it exists, may be used. If the fibre is locally Noetherian, associated points
may replace weakly associated points in the chart and monomorphic conditions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules
namespace RelativeWeakAss

/-- Lemma 71.4.4 (1): let `S` be a scheme, let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`, let `x` be a point of `Points X`, and let `F` be a
quasi-coherent `𝒪_X`-module. The following are equivalent: there exist an étale
scheme chart of `Y` through `f(x)` and a lift of `x` on the residue-field fibre
which is weakly associated to `F` restricted to that fibre; the same holds for
every such chart and lift; there exist étale charts `U → X ×_Y V` as in the
source diagrams such that a lift of `u` to `U_v` is weakly associated to the
restriction of `F`; the same holds for every such diagram; and there exists a
field-valued point of `Y` representing `f(x)` whose fibre has a weakly
associated lift of `x`. -/
@[stacks 0CUZ]
theorem relativeWeakAss_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (F : X.Modules) [F.IsQuasicoherent] (x : Points X) :
    List.TFAE [existsEtale f F x, forallEtale f F x, existsOverPullback f F x,
      forallOverPullback f F x, existsField f F x] :=
  sorry

/-- Lemma 71.4.4 (2): if in addition there is a monomorphism `p₀.hom` from the
spectrum of a field representing `f(x)`, then the conditions of
`relativeWeakAss_tfae` are also equivalent to the unique lift of `x` on the
fibre over `p₀` being weakly associated to the restricted module. -/
@[stacks 0CUZ]
theorem relativeWeakAss_iff_of_mono {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (F : X.Modules) [F.IsQuasicoherent] (x : Points X)
    (p₀ : FieldValuedPoint Y) [Mono p₀.hom]
    (hp₀ : Points.mk p₀ = Points.map f x) :
    ofMono f F x p₀ ↔ existsField f F x :=
  sorry

/-- Lemma 71.4.4 (3): if the fibre of `f` over `f(x)` is locally Noetherian, then
in the étale-chart and fibre-product conditions of `relativeWeakAss_tfae` we may
replace weakly associated points by associated points. -/
@[stacks 0CUZ]
theorem associatedPoints_fiber_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (F : X.Modules) [F.IsQuasicoherent] (x : Points X)
    (hN : LocallyNoetherianFiber.forallEtale f (Points.map f x)) :
    List.TFAE [existsEtale f F x, forallEtale f F x, existsOverPullback f F x,
      forallOverPullback f F x, existsField f F x, existsEtaleAss f F x,
      forallEtaleAss f F x, existsOverPullbackAss f F x, forallOverPullbackAss f F x] :=
  sorry

end RelativeWeakAss
end AlgebraicGeometry.AlgebraicSpace.Modules
