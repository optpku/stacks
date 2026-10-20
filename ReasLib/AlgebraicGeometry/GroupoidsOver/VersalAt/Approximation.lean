module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Versal
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Completion
public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Effective
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreservingOnObjects
public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import ReasLib.RingTheory.Regular.GRing

/-! # Finite-type versal approximations of formal objects -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor IsLocalRing
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids

/-- Canonical morphism `Spec(𝒪_{U,u0} ⧸ m_{u0}^{n+1}) ⟶ U`. -/
def fromSpecStalkPow {U : Scheme.{u}} (u0 : U) (n : ℕ) :
    Spec (CommRingCat.of
        (U.presheaf.stalk u0 ⧸ maximalIdeal (U.presheaf.stalk u0) ^ (n + 1))) ⟶
      U :=
  Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (maximalIdeal (U.presheaf.stalk u0) ^ (n + 1)))) ≫
    U.fromSpecStalk u0

/-- `fromSpecStalkPow` is `Spec` of the quotient map, followed by `fromSpecStalk`. -/
theorem fromSpecStalkPow_eq {U : Scheme.{u}} (u0 : U) (n : ℕ) :
    fromSpecStalkPow u0 n =
      Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (maximalIdeal (U.presheaf.stalk u0) ^ (n + 1)))) ≫
        U.fromSpecStalk u0 :=
  sorry

/-- Restriction morphism `Spec(𝒪_{U,u0} ⧸ m_{u0}^{n+1}) ⟶ U` in `Over S`. -/
def fromSpecStalkPowOverHom {S U : Scheme.{u}} (hU : U ⟶ S) (u0 : U) (n : ℕ) :
    Over.mk (fromSpecStalkPow u0 n ≫ hU) ⟶ Over.mk hU :=
  Over.homMk (fromSpecStalkPow u0 n) rfl

/-- The underlying scheme morphism of `fromSpecStalkPowOverHom` is
`fromSpecStalkPow`. -/
theorem fromSpecStalkPowOverHom_left {S U : Scheme.{u}} (hU : U ⟶ S) (u0 : U)
    (n : ℕ) :
    (fromSpecStalkPowOverHom hU u0 n).left = fromSpecStalkPow u0 n :=
  sorry

/-- Restriction of `x` along `Spec(𝒪_{U,u0} ⧸ m_{u0}^{n+1}) ⟶ U`. -/
def restrictToStalkPow {S : Scheme.{u}} {X : GroupoidsOver S} {U : Scheme.{u}}
    (hU : U ⟶ S) (x : X.total) (hx : X.p.obj x = Over.mk hU) (u0 : U) (n : ℕ) :
    X.total :=
  IsPreFibered.pullbackObj hx (fromSpecStalkPowOverHom hU u0 n)

/-- `restrictToStalkPow` is the chosen cartesian pullback along
`fromSpecStalkPowOverHom`. -/
theorem restrictToStalkPow_eq {S : Scheme.{u}} {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) (n : ℕ) :
    restrictToStalkPow hU x hx u0 n =
      IsPreFibered.pullbackObj hx (fromSpecStalkPowOverHom hU u0 n) :=
  sorry

/-- The restricted object lies over `Spec(𝒪_{U,u0} ⧸ m_{u0}^{n+1}) ⟶ S`. -/
theorem restrictToStalkPow_over {S : Scheme.{u}} {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) (n : ℕ) :
    X.p.obj (restrictToStalkPow hU x hx u0 n) =
      Over.mk (fromSpecStalkPow u0 n ≫ hU) :=
  sorry

/-- Finite-type approximation data of a formal object: a finite type scheme
`U ⟶ S`, a finite type point `u0` with residue field `κ(R)`, and an object `x`
over `U` which is versal at `u0` and whose associated formal object is
isomorphic to `ξ`. The positive truncations are indexed by `n + 1`. -/
structure ApproximateVersal {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} (ξ : FormalObject X) where
  /-- Approximating scheme of finite type over `S`. -/
  U : Scheme.{u}
  /-- Structure morphism `U ⟶ S`. -/
  toS : U ⟶ S
  /-- The structure morphism is of finite type. -/
  finiteType : Scheme.Hom.FiniteType toS
  /-- Finite type point of `U` at which the approximating object is versal. -/
  u0 : U
  /-- The chosen point is of finite type. -/
  isFiniteTypePoint : IsFiniteTypePoint u0
  /-- Identification `κ(u0) ≃+* κ(R)` of residue fields. -/
  residueIso : residueFieldType u0 ≃+* ResidueField ξ.base.carrier
  /-- `Spec(κ(u0)) ⟶ S` agrees with `Spec(κ(R)) ⟶ S` after `residueIso`. -/
  residueIso_over :
    fromResidueField u0 ≫ toS =
      Spec.map (CommRingCat.ofHom residueIso.symm.toRingHom) ≫
        FormalObject.residueToS ξ
  /-- Approximating object of `X`. -/
  object : X.total
  /-- The approximating object lies over `U ⟶ S`. -/
  over_obj : X.p.obj object = Over.mk toS
  /-- The approximating object is versal at the chosen point. -/
  isVersalAt :
    -- Local instance justification (proof-local temporary data): the canonical pointwise-versality and completed-stalk APIs take finiteness proofs as class arguments; these bindings pass exactly the immutable proofs stored in this explicit approximation record, with no new inference rule.
    letI : Scheme.Hom.FiniteType toS := finiteType
    IsVersalAt toS object over_obj u0
  /-- The formal object of `x` over `𝒪_{U,u0}^∧` is isomorphic to `ξ`. -/
  associatedIso :
    -- Local instance justification (proof-local temporary data): the canonical pointwise-versality and completed-stalk APIs take finiteness proofs as class arguments; these bindings pass exactly the immutable proofs stored in this explicit approximation record, with no new inference rule.
    letI : Scheme.Hom.FiniteType toS := finiteType
    -- Local instance justification (proof-local temporary data): the canonical pointwise-versality and completed-stalk APIs take finiteness proofs as class arguments; these bindings pass exactly the immutable proofs stored in this explicit approximation record, with no new inference rule.
    letI : IsFiniteTypePoint u0 := isFiniteTypePoint
    associatedFormalObject toS object over_obj u0 ≅ ξ

namespace ApproximateVersal

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
variable {ξ : FormalObject X}

/-- Package finite-type approximation data of a formal object. -/
def of (U : Scheme.{u}) (toS : U ⟶ S) [Scheme.Hom.FiniteType toS] (u0 : U)
    [IsFiniteTypePoint u0]
    (residueIso : residueFieldType u0 ≃+* ResidueField ξ.base.carrier)
    (residueIso_over :
      fromResidueField u0 ≫ toS =
        Spec.map (CommRingCat.ofHom residueIso.symm.toRingHom) ≫
          FormalObject.residueToS ξ)
    (object : X.total) (over_obj : X.p.obj object = Over.mk toS)
    [IsVersalAt toS object over_obj u0]
    (associatedIso : associatedFormalObject toS object over_obj u0 ≅ ξ) :
    ApproximateVersal ξ where
  U := U
  toS := toS
  finiteType := inferInstance
  u0 := u0
  isFiniteTypePoint := inferInstance
  residueIso := residueIso
  residueIso_over := residueIso_over
  object := object
  over_obj := over_obj
  isVersalAt := inferInstance
  associatedIso := associatedIso

/-- Conditions encoded by approximation data: finite type structure
morphism, finite type point, residue-field identification over `S`, object over
`U`, versality at `u0`, and isomorphism of associated formal objects. -/
theorem spec (W : ApproximateVersal ξ) :
    -- Local instance justification (proof-local temporary data): the canonical pointwise-versality and completed-stalk APIs take finiteness proofs as class arguments; these bindings pass exactly the immutable proofs stored in this explicit approximation record, with no new inference rule.
    letI : Scheme.Hom.FiniteType W.toS := W.finiteType
    -- Local instance justification (proof-local temporary data): the canonical pointwise-versality and completed-stalk APIs take finiteness proofs as class arguments; these bindings pass exactly the immutable proofs stored in this explicit approximation record, with no new inference rule.
    letI : IsFiniteTypePoint W.u0 := W.isFiniteTypePoint
    Scheme.Hom.FiniteType W.toS ∧
      IsFiniteTypePoint W.u0 ∧
        (fromResidueField W.u0 ≫ W.toS =
          Spec.map (CommRingCat.ofHom W.residueIso.symm.toRingHom) ≫
            FormalObject.residueToS ξ) ∧
          X.p.obj W.object = Over.mk W.toS ∧
            IsVersalAt W.toS W.object W.over_obj W.u0 ∧
              Nonempty
                (associatedFormalObject W.toS W.object W.over_obj W.u0 ≅ ξ) :=
  sorry

/-- The approximating object restricted to
`Spec(𝒪_{U,u0} ⧸ m_{u0}^{n+1})` is isomorphic to `ξ.objects n` over `S`. -/
theorem exists_restrictIso (W : ApproximateVersal ξ) (n : ℕ) :
    ∃ (e : restrictToStalkPow W.toS W.object W.over_obj W.u0 n ≅ ξ.objects n)
      (f : Over.mk (fromSpecStalkPow W.u0 n ≫ W.toS) ⟶ ξ.base.stageOver n),
      X.p.IsHomLift f e.hom :=
  sorry

end ApproximateVersal

/-- A versal effective formal object over a locally Noetherian scheme admits a
finite-type approximation versal at a finite type point with the same residue
field and isomorphic associated formal object, if the local ring at the residue
image is a G-ring and the structure morphism is limit preserving on objects. -/
theorem nonempty_approximateVersal {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S}
    [LimitPreservingOnObjects (baseProjection.{u + 1, u, u + 1} X)]
    (ξ : FormalObject X) (s : S)
    (hs : ξ.base.toS (closedPoint ξ.base.carrier) = s)
    [IsGRing (S.presheaf.stalk s)] [FormalObject.IsEffective ξ]
    (h_versal : FormalObject.IsVersalOnObjects ξ) :
    Nonempty (ApproximateVersal ξ) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
