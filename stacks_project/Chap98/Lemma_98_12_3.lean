/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Definition_90_27_1_MinimalVersal
public import stacks_project.Chap98.Definition_98_13_1_Versal
public import stacks_project.Chap98.Lemma_98_12_3_Associated
public import stacks_project.Chap98.Remark_98_9_2_Predeformation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Versality at a finite type point versus versality of the associated formal object

In the setup of Definition 98.12.2, the object `x` is versal at `u0` if and only
if the formal object of `X` over `𝒪_{U,u0}^∧` associated to the restriction of
`x` to `Spec(𝒪_{U,u0}^∧)` is versal.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor IsLocalRing
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- The Chap90 predeformation projection of the associated formal object is
cofibered in groupoids. -/
instance instIsFiberedInGroupoidsOp_toPredeformation
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0]
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ (associatedFormalObject hU x hx u0).base.carrier]
    [Module.Finite Λ
      (ResidueField (associatedFormalObject hU x hx u0).base.carrier)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (h_toS :
      Spec.map (CommRingCat.ofHom
            (algebraMap Λ (associatedFormalObject hU x hx u0).base.carrier)) ≫
          openImmersion =
        (associatedFormalObject hU x hx u0).base.toS) :
    Functor.IsFibered.InGroupoids
      (FormalObject.predeformationProjection
        (associatedFormalObject hU x hx u0) openImmersion h_toS).op :=
  sorry

/-- Lemma 98.12.3: with notation as in Definition 98.12.2, let `R` be the
completion `𝒪_{U,u0}^∧` and let `ξ` be the formal object of `X` over `R`
associated to `x` restricted to `Spec(R)` via 98.9.3.1. Then `x` is versal at
`u0` if and only if `ξ` is versal. -/
@[stacks 0CXK]
theorem isVersalAt_iff_isVersal {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU]
    (x : X.total) (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0] :
    IsVersalAt hU x hx u0 ↔
      ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
        [Algebra Λ (associatedFormalObject hU x hx u0).base.carrier]
        [Module.Finite Λ
          (ResidueField (associatedFormalObject hU x hx u0).base.carrier)]
        (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
        [IsOpenImmersion openImmersion]
        (h_toS :
          Spec.map (CommRingCat.ofHom
                (algebraMap Λ
                  (associatedFormalObject hU x hx u0).base.carrier)) ≫
              openImmersion =
            (associatedFormalObject hU x hx u0).base.toS),
        _root_.FormalObject.IsVersal
          (FormalObject.toPredeformation
            (associatedFormalObject hU x hx u0) openImmersion h_toS) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
