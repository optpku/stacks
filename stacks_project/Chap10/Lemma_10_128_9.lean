/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.EssentialFiniteness.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
import StacksCheckRecall

/-!
@stack 05UV
-/

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open scoped TensorProduct Algebra.TensorProduct.Right

universe u v w x

section

variable {R : Type u} {S : Type v} {S' : Type w} {M : Type x}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
variable [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
variable [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')]
variable [AddCommGroup M] [Module S' M] [Module.FinitePresentation S' M]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S
local notation "ClosedFiberModule" => ClosedFiber ⊗[S] RestrictScalars S S' M

/- Domain-style sampling for Lemma 10.128.9:
* primary domain: local commutative algebra of essential finite presentation and fiberwise
  flatness along a local tower `R → S → S'`;
* sampled owner declarations:
  `Algebra.EssFiniteType`,
  `Algebra.EssFinitePresentation`,
  `Ideal.Fiber`,
  `RingHom.Flat.ClosedFiber.of_essFinitePresentation`,
  `Module.Flat.ClosedFiber.of_essFinitePresentation`;
* best owner abstraction: the new source-facing content is the upgrade
  `Algebra.EssFiniteType R S ⟶ Algebra.EssFinitePresentation R S` under fiberwise flatness
  hypotheses, while the closed fiber itself should live on the canonical owners
  `ClosedFiber = Ideal.Fiber (maximalIdeal R) S` and
  `ClosedFiberModule = ClosedFiber ⊗[S] RestrictScalars S S' M`.

Primitive data vs. derived API:
* primitive data: the local tower `R → S → S'`, the essential finite type hypothesis on `R → S`,
  the essential finite presentation hypothesis on `R → S'`, the finitely presented `S'`-module
  `M`, flatness of `ClosedFiberModule` over `ClosedFiber`, and flatness of `M` over `R` after
  restriction of scalars along `R → S'`;
* derived API: essential finite presentation of `R → S`, then the flatness conclusions from
  Lemma `10.128.8`.

Source/core/bridge triage:
* `source-facing`: the first theorem below, which is the extra Stacks content of Lemma `10.128.9`;
* `core/canonical`: `Algebra.EssFiniteType`, `Algebra.EssFinitePresentation`, `Ideal.Fiber`,
  `Module.Flat`, and `RingHom.Flat`;
* `bridge/view`: the quotient presentation
  `M ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M))` of the canonical
  closed-fiber module after restricting scalars from `S'` to `S`.
-/

/-- Lemma 10.128.9 (1): if `R → S → S'` are local ring homomorphisms, `R → S'` is essentially of
finite presentation, `R → S` is essentially of finite type, `M` is a nonzero finitely presented
`S'`-module, the canonical closed-fiber module
`ClosedFiberModule = ((maximalIdeal R).Fiber S) ⊗[S] M`, equivalently `M / 𝔪_R M`, is flat over
the canonical closed-fiber ring `ClosedFiber = (maximalIdeal R).Fiber S`, equivalently
`S / 𝔪_R S`, and `M` is flat over `R`, then `R → S` is essentially of finite presentation. -/
@[stacks 05UV "(1) middle map essentially finitely presented"]
theorem middleRing_essFinitePresentation_of_essFiniteType_of_flat_closedFiber_and_flat_over_base
    (hM : Nontrivial M) (hRS : Algebra.EssFiniteType R S)
    (hRS' : Algebra.EssFinitePresentation R S')
    (hflat_closedFiber : Module.Flat ClosedFiber ClosedFiberModule)
    (hflat_R : Module.Flat R (RestrictScalars R S' M)) :
    Algebra.EssFinitePresentation R S := sorry

/-- Under the hypotheses of Lemma 10.128.9, the local homomorphism `R → S` is flat. -/
@[stacks 05UV "(2) middle map flat"]
theorem algebraMap_flat_of_essFiniteType_of_flat_closedFiber_and_flat_over_base
    (hM : Nontrivial M) (hRS : Algebra.EssFiniteType R S)
    (hRS' : Algebra.EssFinitePresentation R S')
    (hflat_closedFiber : Module.Flat ClosedFiber ClosedFiberModule)
    (hflat_R : Module.Flat R (RestrictScalars R S' M)) :
    (algebraMap R S).Flat := sorry

/-- Under the hypotheses of Lemma 10.128.9, the `S'`-module `M` is flat over `S`. -/
@[stacks 05UV "(3) module flat over the middle ring"]
theorem flat_over_middleRing_of_essFiniteType_of_flat_closedFiber_and_flat_over_base
    (hRS : Algebra.EssFiniteType R S) (hRS' : Algebra.EssFinitePresentation R S')
    (hflat_closedFiber : Module.Flat ClosedFiber ClosedFiberModule)
    (hflat_R : Module.Flat R (RestrictScalars R S' M)) :
    Module.Flat S (RestrictScalars S S' M) := sorry

end

#check @Algebra.EssFiniteType
#check @Algebra.EssFinitePresentation
#check @Ideal.Fiber
