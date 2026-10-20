module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Versal
public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt.Approximation
public import stacks_project.Chap98.Lemma_98_12_7
public import stacks_project.Chap98.Definition_98_13_1_Versal

/-! # Compatibility checks for finite-type versal approximation -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor IsLocalRing
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

#check (AlgebraicGeometry.GroupoidsOver.fromSpecStalkPow :
  ∀ {U : Scheme.{u}} (u0 : U) (n : ℕ),
    Spec (CommRingCat.of
        (U.presheaf.stalk u0 ⧸ maximalIdeal (U.presheaf.stalk u0) ^ (n + 1))) ⟶
      U)

#check (AlgebraicGeometry.GroupoidsOver.fromSpecStalkPow_eq :
  ∀ {U : Scheme.{u}} (u0 : U) (n : ℕ),
    fromSpecStalkPow u0 n =
      Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (maximalIdeal (U.presheaf.stalk u0) ^ (n + 1)))) ≫
        U.fromSpecStalk u0)

#check (AlgebraicGeometry.GroupoidsOver.fromSpecStalkPowOverHom :
  ∀ {S U : Scheme.{u}} (hU : U ⟶ S) (u0 : U) (n : ℕ),
    Over.mk (fromSpecStalkPow u0 n ≫ hU) ⟶ Over.mk hU)

#check (AlgebraicGeometry.GroupoidsOver.fromSpecStalkPowOverHom_left :
  ∀ {S U : Scheme.{u}} (hU : U ⟶ S) (u0 : U)
    (n : ℕ),
    (fromSpecStalkPowOverHom hU u0 n).left = fromSpecStalkPow u0 n)

#check (AlgebraicGeometry.GroupoidsOver.restrictToStalkPow :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} {U : Scheme.{u}}
    (hU : U ⟶ S) (x : X.total) (hx : X.p.obj x = Over.mk hU) (u0 : U) (n : ℕ),
    X.total)

#check (AlgebraicGeometry.GroupoidsOver.restrictToStalkPow_eq :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) (n : ℕ),
    restrictToStalkPow hU x hx u0 n =
      IsPreFibered.pullbackObj hx (fromSpecStalkPowOverHom hU u0 n))

#check (AlgebraicGeometry.GroupoidsOver.restrictToStalkPow_over :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) (n : ℕ),
    X.p.obj (restrictToStalkPow hU x hx u0 n) =
      Over.mk (fromSpecStalkPow u0 n ≫ hU))

#check (AlgebraicGeometry.GroupoidsOver.FormalObject.instIsFiberedInGroupoidsOp_toPredeformation :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    (ξ : FormalObject X) {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ ξ.base.carrier]
    [Module.Finite Λ (ResidueField ξ.base.carrier)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (h_toS :
      Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.carrier)) ≫
          openImmersion =
        ξ.base.toS),
    Functor.IsFibered.InGroupoids
      (FormalObject.predeformationProjection ξ openImmersion h_toS).op)

#check (AlgebraicGeometry.GroupoidsOver.FormalObject.IsVersalOnObjects :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} (ξ : FormalObject X),
    Prop)

#check (AlgebraicGeometry.GroupoidsOver.FormalObject.isVersalOnObjects_iff :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} (ξ : FormalObject X),
    FormalObject.IsVersalOnObjects ξ ↔
      ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
        [Algebra Λ ξ.base.carrier]
        [Module.Finite Λ (ResidueField ξ.base.carrier)]
        (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
        [IsOpenImmersion openImmersion]
        (h_toS :
          Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.carrier)) ≫
              openImmersion =
            ξ.base.toS),
        _root_.FormalObject.IsVersal (FormalObject.toPredeformation ξ openImmersion h_toS))

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
variable {ξ : FormalObject X}

#check (AlgebraicGeometry.GroupoidsOver.ApproximateVersal.spec :
  ∀ (W : ApproximateVersal ξ),
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
                (associatedFormalObject W.toS W.object W.over_obj W.u0 ≅ ξ))

#check (AlgebraicGeometry.GroupoidsOver.ApproximateVersal.exists_restrictIso :
  ∀ (W : ApproximateVersal ξ) (n : ℕ),
    ∃ (e : restrictToStalkPow W.toS W.object W.over_obj W.u0 n ≅ ξ.objects n)
      (f : Over.mk (fromSpecStalkPow W.u0 n ≫ W.toS) ⟶ ξ.base.stageOver n),
      X.p.IsHomLift f e.hom)

#check (AlgebraicGeometry.GroupoidsOver.ApproximateVersal :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S} (ξ : FormalObject X),
    Type (u + 1))

#check (AlgebraicGeometry.GroupoidsOver.ApproximateVersal.of :
  ∀ (U : Scheme.{u}) (toS : U ⟶ S) [Scheme.Hom.FiniteType toS] (u0 : U)
    [IsFiniteTypePoint u0]
    (residueIso : residueFieldType u0 ≃+* ResidueField ξ.base.carrier)
    (residueIso_over :
      fromResidueField u0 ≫ toS =
        Spec.map (CommRingCat.ofHom residueIso.symm.toRingHom) ≫
          FormalObject.residueToS ξ)
    (object : X.total) (over_obj : X.p.obj object = Over.mk toS)
    [IsVersalAt toS object over_obj u0]
    (associatedIso : associatedFormalObject toS object over_obj u0 ≅ ξ),
    ApproximateVersal ξ)

end AlgebraicGeometry.GroupoidsOver
