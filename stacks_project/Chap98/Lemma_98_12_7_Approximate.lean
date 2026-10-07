module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import stacks_project.Chap90.Definition_90_27_1_MinimalVersal
public import stacks_project.Chap98.Definition_98_13_1_Versal
public import stacks_project.Chap98.Lemma_98_12_3_Associated
public import stacks_project.Chap98.Remark_98_9_2_Predeformation

/-!
# Finite-type approximations of versal effective formal objects

A versal effective formal object `ξ` of a category fibred in groupoids over a
locally Noetherian base may be approximated by an object `x` over a finite type
scheme `U → S`, versal at a finite type point `u0` with residue field `κ(R)`,
and with associated formal object isomorphic to `ξ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor IsLocalRing
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- Canonical morphism `Spec(𝒪_{U,u0} ⧸ m_{u0}^{n+1}) ⟶ U`. Lean stage `n`
corresponds to the source truncation of order `n+1`. -/
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

namespace FormalObject

/-- The Chap90 predeformation projection of a scheme-level formal object is
cofibered in groupoids. -/
instance instIsFiberedInGroupoidsOp_toPredeformation
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    (ξ : FormalObject X) {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ ξ.base.carrier]
    [Module.Finite Λ (ResidueField ξ.base.carrier)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (h_toS :
      Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.carrier)) ≫
          openImmersion =
        ξ.base.toS) :
    Functor.IsFibered.InGroupoids
      (predeformationProjection ξ openImmersion h_toS).op :=
  sorry

/-- A scheme-level formal object is versal when, after every affine-open
factorization of `Spec(R) ⟶ S`, the associated Chap90 formal object of
`ℱ_{X, κ(R), ξ₁}` is versal. -/
def IsVersalOnObjects {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} (ξ : FormalObject X) : Prop :=
  ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ ξ.base.carrier]
    [Module.Finite Λ (ResidueField ξ.base.carrier)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    [IsOpenImmersion openImmersion]
    (h_toS :
      Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.carrier)) ≫
          openImmersion =
        ξ.base.toS),
    _root_.FormalObject.IsVersal (toPredeformation ξ openImmersion h_toS)

/-- Versality of a scheme-level formal object is Chap90 versality of
`toPredeformation` on every affine-open factorization. -/
theorem isVersalOnObjects_iff {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} (ξ : FormalObject X) :
    IsVersalOnObjects ξ ↔
      ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
        [Algebra Λ ξ.base.carrier]
        [Module.Finite Λ (ResidueField ξ.base.carrier)]
        (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
        [IsOpenImmersion openImmersion]
        (h_toS :
          Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.carrier)) ≫
              openImmersion =
            ξ.base.toS),
        _root_.FormalObject.IsVersal (toPredeformation ξ openImmersion h_toS) :=
  sorry

end FormalObject

/-- Finite-type approximation data of a formal object: a finite type scheme
`U ⟶ S`, a finite type point `u0` with residue field `κ(R)`, and an object `x`
over `U` which is versal at `u0` and whose associated formal object is
isomorphic to `ξ`. Lean stage `n` is the source object `ξ_{n+1}` over
`Spec(R ⧸ m^{n+1})` and `Spec(𝒪_{U,u0} ⧸ m_{u0}^{n+1})`. -/
structure ApproximateVersal {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} (ξ : FormalObject X) where
  /-- Approximating scheme of finite type over `S`. -/
  U : Scheme.{u}
  /-- Structure morphism `U ⟶ S`. -/
  toS : U ⟶ S
  [finiteType : Scheme.Hom.FiniteType toS]
  /-- Finite type point of `U` at which the approximating object is versal. -/
  u0 : U
  [isFiniteTypePoint : IsFiniteTypePoint u0]
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
  [isVersalAt : IsVersalAt toS object over_obj u0]
  /-- The formal object of `x` over `𝒪_{U,u0}^∧` is isomorphic to `ξ`. -/
  associatedIso : associatedFormalObject toS object over_obj u0 ≅ ξ

attribute [instance] ApproximateVersal.finiteType
  ApproximateVersal.isFiniteTypePoint ApproximateVersal.isVersalAt

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
  u0 := u0
  residueIso := residueIso
  residueIso_over := residueIso_over
  object := object
  over_obj := over_obj
  associatedIso := associatedIso

/-- Source conditions encoded by approximation data: finite type structure
morphism, finite type point, residue-field identification over `S`, object over
`U`, versality at `u0`, and isomorphism of associated formal objects. -/
theorem spec (W : ApproximateVersal ξ) :
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

/-- Existence of approximation data is equivalent to the source conditions of a
finite type `U ⟶ S`, a finite type point `u0` with residue field `κ(R)`, and an
object over `U` versal at `u0` whose associated formal object is isomorphic to
`ξ`. -/
theorem spec_iff :
    Nonempty (ApproximateVersal ξ) ↔
      ∃ W : ApproximateVersal ξ,
        Scheme.Hom.FiniteType W.toS ∧
          IsFiniteTypePoint W.u0 ∧
            (fromResidueField W.u0 ≫ W.toS =
              Spec.map (CommRingCat.ofHom W.residueIso.symm.toRingHom) ≫
                FormalObject.residueToS ξ) ∧
              X.p.obj W.object = Over.mk W.toS ∧
                IsVersalAt W.toS W.object W.over_obj W.u0 ∧
                  Nonempty
                    (associatedFormalObject W.toS W.object W.over_obj W.u0 ≅
                      ξ) :=
  sorry

/-- Source restriction clause: `x` restricted to
`Spec(𝒪_{U,u0} ⧸ m_{u0}^{n+1})` is isomorphic to `ξ.objects n` over `S`. -/
theorem exists_restrictIso (W : ApproximateVersal ξ) (n : ℕ) :
    ∃ (e : restrictToStalkPow W.toS W.object W.over_obj W.u0 n ≅ ξ.objects n)
      (f : Over.mk (fromSpecStalkPow W.u0 n ≫ W.toS) ⟶ ξ.base.stageOver n),
      X.p.IsHomLift f e.hom :=
  sorry

end ApproximateVersal

end AlgebraicGeometry.GroupoidsOver
