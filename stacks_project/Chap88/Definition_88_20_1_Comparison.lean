module

public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import stacks_project.Chap88.Definition_88_20_1_LocallyNoetherian
public import stacks_project.Chap88.Definition_88_20_1_Ring

/-!
# Affine formal algebraic spaces induced by adic Noetherian homomorphisms

A morphism of affine formal algebraic spaces corresponds to a continuous
homomorphism `φ : A →+* B` of adic Noetherian topological rings when the
source (resp. target) is a directed affine thickening of successive quotient
spectra of `B` (resp. `A`), and the morphism is the contravariant colimit of
`Spec` of the finite-level quotient maps of `φ`. The correspondence is
contravariant: `φ : A →+* B` induces a map from the thickening of `B` to the
thickening of `A`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- The affine thickening `Spec(A ⧸ I ^ (n + 1))`, viewed as a scheme over `S`
via the structure morphism of `Spec(A)`. -/
def adicStage (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) ≫
    structureHom)

/-- The underlying scheme of `adicStage A I n structureHom` is
`Spec(A ⧸ I ^ (n + 1))`. -/
theorem adicStage_left (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ)
    {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S) :
    (adicStage A I n structureHom).left = Spec (.of (A ⧸ I ^ (n + 1))) :=
  sorry

/-- The successor thickening
`Spec(A ⧸ I ^ (n + 1)) ⟶ Spec(A ⧸ I ^ (n + 2))` over `S`. -/
def adicSucc (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S) :
    adicStage A I n structureHom ⟶ adicStage A I (n + 1) structureHom :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n + 1))))
    sorry

/-- The underlying scheme morphism of `adicSucc` is `Spec.map` of
`Ideal.Quotient.factorPowSucc`. -/
theorem adicSucc_left (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ)
    {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S) :
    (adicSucc A I n structureHom).left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n + 1))) :=
  sorry

/-- The `ℕ`-indexed diagram of affine thickenings `Spec(A ⧸ I ^ (n + 1))`
over `S`. -/
def adicThickenings (A : Type u) [CommRing A] (I : Ideal A) {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S) : ℕ ⥤ Over S :=
  Functor.ofSequence fun n ↦ adicSucc A I n structureHom

/-- Objects of `adicThickenings A I structureHom` are the stages
`adicStage A I n structureHom`. -/
theorem adicThickenings_obj (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ)
    {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S) :
    (adicThickenings A I structureHom).obj n = adicStage A I n structureHom :=
  sorry

/-- The morphism of affine thickenings induced by `φ : A →+* B` at infinitesimal
order `n`, using `Ideal.quotientMap` on the compatible powers of ideals of
definition. -/
def adicStageMap {A B : Type u} [CommRing A] [CommRing B] {I : Ideal A}
    {J : Ideal B} (φ : A →+* B)
    (hpow : ∀ n : ℕ, I ^ (n + 1) ≤ (J ^ (n + 1)).comap φ) (n : ℕ)
    {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) :
    adicStage B J n (Spec.map (CommRingCat.ofHom φ) ≫ hA) ⟶
      adicStage A I n hA :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (J ^ (n + 1)) φ (hpow n))))
    sorry

/-- The underlying scheme morphism of `adicStageMap` is `Spec.map` of
`Ideal.quotientMap` applied to `φ`. -/
theorem adicStageMap_left {A B : Type u} [CommRing A] [CommRing B] {I : Ideal A}
    {J : Ideal B} (φ : A →+* B)
    (hpow : ∀ n : ℕ, I ^ (n + 1) ≤ (J ^ (n + 1)).comap φ) (n : ℕ)
    {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) :
    (adicStageMap φ hpow n hA).left =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap (J ^ (n + 1)) φ (hpow n))) :=
  sorry

/-- The morphism of thickening diagrams induced by `φ : A →+* B`. -/
def adicThickeningsMap {A B : Type u} [CommRing A] [CommRing B] {I : Ideal A}
    {J : Ideal B} (φ : A →+* B)
    (hpow : ∀ n : ℕ, I ^ (n + 1) ≤ (J ^ (n + 1)).comap φ) {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S) :
    adicThickenings B J (Spec.map (CommRingCat.ofHom φ) ≫ hA) ⟶
      adicThickenings A I hA :=
  NatTrans.ofSequence (fun n ↦ adicStageMap φ hpow n hA) sorry

/-- Components of `adicThickeningsMap` are the stage maps induced by
`Ideal.quotientMap` of `φ`. -/
theorem adicThickeningsMap_app {A B : Type u} [CommRing A] [CommRing B]
    {I : Ideal A} {J : Ideal B} (φ : A →+* B)
    (hpow : ∀ n : ℕ, I ^ (n + 1) ≤ (J ^ (n + 1)).comap φ) (n : ℕ)
    {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) :
    (adicThickeningsMap φ hpow hA).app n = adicStageMap φ hpow n hA :=
  sorry

/-- An arrow `g : U ⟶ V` of affine formal algebraic spaces over `S` is induced
by a continuous homomorphism `φ : A →+* B` of adic Noetherian rings when `U`
is the directed affine thickening of successive quotient spectra of `B`, `V`
is the corresponding thickening for `A`, the target ideal is compatible with
`φ(I)B`, the finite-level maps are `Ideal.quotientMap` of `φ`, and `g` is
compatible with those `Spec` maps via fppf-local comparisons from the Yoneda
presheaf colimits. -/
def IsInducedBy {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u} (g : U ⟶ V)
    {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (φ : A →+* B) : Prop :=
  Continuous φ ∧
    ∃ (I : Ideal A) (J : Ideal B),
      TopologicalRing.Ideal.IsIdealOfDefinition I ∧
        TopologicalRing.Ideal.IsIdealOfDefinition J ∧
          Ideal.map φ I ≤ J ∧
            ∃ (hpow : ∀ n : ℕ, I ^ (n + 1) ≤ (J ^ (n + 1)).comap φ)
              (hA : Spec (.of A) ⟶ S),
        FormalAlgebraicSpace.IsDirectedAffineThickeningColimit
            (adicThickenings B J (Spec.map (CommRingCat.ofHom φ) ≫ hA)) U ∧
          FormalAlgebraicSpace.IsDirectedAffineThickeningColimit
              (adicThickenings A I hA) V ∧
            ∃ (cU : Cocone
                (adicThickenings B J (Spec.map (CommRingCat.ofHom φ) ≫ hA) ⋙
                  yoneda))
              (cV : Cocone (adicThickenings A I hA ⋙ yoneda))
              (ηU : cU.pt ⟶ U) (ηV : cV.pt ⟶ V),
                Nonempty (IsColimit cU) ∧ Nonempty (IsColimit cV) ∧
                  Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) ηU ∧
                    Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) ηU ∧
                      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) ηV ∧
                        Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) ηV ∧
                          ∀ n : ℕ,
                            cU.ι.app n ≫ ηU ≫ g =
                              yoneda.map ((adicThickeningsMap φ hpow hA).app n) ≫
                                cV.ι.app n ≫ ηV

/-- The inducing predicate unpacks as continuity of `φ`, compatibility of an
ideal of definition of `B` with `φ(I)B`, finite-level `Ideal.quotientMap`
maps, and an fppf-local comparison from the Yoneda presheaf colimits. -/
theorem isInducedBy_iff {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u} (g : U ⟶ V)
    {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (φ : A →+* B) :
    IsInducedBy g φ ↔
      Continuous φ ∧
        ∃ (I : Ideal A) (J : Ideal B),
          TopologicalRing.Ideal.IsIdealOfDefinition I ∧
            TopologicalRing.Ideal.IsIdealOfDefinition J ∧
              Ideal.map φ I ≤ J ∧
                ∃ (hpow : ∀ n : ℕ, I ^ (n + 1) ≤ (J ^ (n + 1)).comap φ)
                  (hA : Spec (.of A) ⟶ S),
            FormalAlgebraicSpace.IsDirectedAffineThickeningColimit
                (adicThickenings B J (Spec.map (CommRingCat.ofHom φ) ≫ hA)) U ∧
              FormalAlgebraicSpace.IsDirectedAffineThickeningColimit
                  (adicThickenings A I hA) V ∧
                ∃ (cU : Cocone
                    (adicThickenings B J (Spec.map (CommRingCat.ofHom φ) ≫ hA) ⋙
                      yoneda))
                  (cV : Cocone (adicThickenings A I hA ⋙ yoneda))
                  (ηU : cU.pt ⟶ U) (ηV : cV.pt ⟶ V),
                    Nonempty (IsColimit cU) ∧ Nonempty (IsColimit cV) ∧
                      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) ηU ∧
                        Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) ηU ∧
                          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) ηV ∧
                            Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) ηV ∧
                              ∀ n : ℕ,
                                cU.ι.app n ≫ ηU ≫ g =
                                  yoneda.map ((adicThickeningsMap φ hpow hA).app n) ≫
                                    cV.ι.app n ≫ ηV :=
  sorry

/-- If `g` is induced by `φ : A →+* B`, the source of `g` is presented by
successive quotient spectra of `B`. -/
theorem domain_of {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u} {g : U ⟶ V}
    {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] {φ : A →+* B}
    (h : IsInducedBy g φ) :
    ∃ (J : Ideal B) (_ : TopologicalRing.Ideal.IsIdealOfDefinition J)
      (hB : Spec (.of B) ⟶ S),
        FormalAlgebraicSpace.IsDirectedAffineThickeningColimit
          (adicThickenings B J hB) U :=
  sorry

/-- If `g` is induced by `φ : A →+* B`, the target of `g` is presented by
successive quotient spectra of `A`. -/
theorem codomain_of {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u} {g : U ⟶ V}
    {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] {φ : A →+* B}
    (h : IsInducedBy g φ) :
    ∃ (I : Ideal A) (_ : TopologicalRing.Ideal.IsIdealOfDefinition I)
      (hA : Spec (.of A) ⟶ S),
        FormalAlgebraicSpace.IsDirectedAffineThickeningColimit
          (adicThickenings A I hA) V :=
  sorry

/-- A morphism of affine formal algebraic spaces is rig-étale when it is induced
by a rig-étale continuous homomorphism of adic Noetherian topological rings. -/
class RigEtale {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace U]
    [FormalAlgebraicSpace.IsAffine U]
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace V]
    [FormalAlgebraicSpace.IsAffine V]
    (g : U ⟶ V) : Prop where
  /-- There is a rig-étale homomorphism of adic Noetherian rings inducing `g`. -/
  exists_hom :
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B)
      (_ : TopologicalSpace A) (_ : TopologicalSpace B)
      (_ : TopologicalRing.IsAdicRing A) (_ : TopologicalRing.IsAdicRing B)
      (_ : IsNoetherianRing A) (_ : IsNoetherianRing B)
      (φ : A →+* B),
        RingHom.RigEtale φ ∧ IsInducedBy g φ

namespace RigEtale

/-- The identity of a Noetherian affine formal algebraic space is rig-étale. -/
instance id {S : Scheme.{u}} {U : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace U]
    [FormalAlgebraicSpace.IsAffine U]
    [FormalAlgebraicSpace.IsNoetherianAffine U] : RigEtale (𝟙 U) :=
  sorry

/-- A morphism induced by a rig-étale homomorphism of adic Noetherian rings is
rig-étale. -/
theorem ofHom {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace U]
    [FormalAlgebraicSpace.IsAffine U]
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace V]
    [FormalAlgebraicSpace.IsAffine V]
    (g : U ⟶ V) {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (φ : A →+* B)
    [RingHom.RigEtale φ] (hg : IsInducedBy g φ) : RigEtale g :=
  sorry

/-- A rig-étale morphism of affine formal algebraic spaces is induced by a
rig-étale homomorphism of adic Noetherian rings. -/
theorem spec {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace U]
    [FormalAlgebraicSpace.IsAffine U]
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace V]
    [FormalAlgebraicSpace.IsAffine V]
    (g : U ⟶ V) [RigEtale g] :
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B)
      (_ : TopologicalSpace A) (_ : TopologicalSpace B)
      (_ : TopologicalRing.IsAdicRing A) (_ : TopologicalRing.IsAdicRing B)
      (_ : IsNoetherianRing A) (_ : IsNoetherianRing B)
      (φ : A →+* B),
        RingHom.RigEtale φ ∧ IsInducedBy g φ :=
  sorry

end RigEtale

end AlgebraicGeometry.AffineFormalAlgebraicSpace
