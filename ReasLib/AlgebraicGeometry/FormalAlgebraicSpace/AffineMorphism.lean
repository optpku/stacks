module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Basic
public import ReasLib.AlgebraicGeometry.FormalSpectrum.PowerStages
public import ReasLib.RingTheory.Topology.Adic.Complete
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Ring homomorphisms inducing morphisms of affine formal algebraic spaces

Compatible quotient-ring maps induce morphisms of canonical power-thickening diagrams.
Their Yoneda colimits describe the contravariant ring-to-formal-space correspondence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- The quotient-ring map induced by a homomorphism commutes with the structure maps
of the corresponding power stages to the base scheme. -/
theorem adicStageMap_comm {A B : Type u} [CommRing A] [CommRing B] {I : Ideal A}
    {J : Ideal B} (φ : A →+* B)
    (hpow : ∀ n : ℕ, I ^ (n + 1) ≤ (J ^ (n + 1)).comap φ) (n : ℕ)
    {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) :
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap (J ^ (n + 1)) φ (hpow n))) ≫
      (powerStage hA I n).hom =
        (powerStage (Spec.map (CommRingCat.ofHom φ) ≫ hA) J n).hom :=
  sorry

/-- The morphism of affine thickenings induced by `φ : A →+* B` at infinitesimal
order `n`, using `Ideal.quotientMap` on the compatible powers of ideals of
definition. -/
def adicStageMap {A B : Type u} [CommRing A] [CommRing B] {I : Ideal A}
    {J : Ideal B} (φ : A →+* B)
    (hpow : ∀ n : ℕ, I ^ (n + 1) ≤ (J ^ (n + 1)).comap φ) (n : ℕ)
    {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) :
    powerStage (Spec.map (CommRingCat.ofHom φ) ≫ hA) J n ⟶
      powerStage hA I n :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (J ^ (n + 1)) φ (hpow n))))
    (adicStageMap_comm φ hpow n hA)

/-- The underlying scheme morphism of `adicStageMap` is `Spec.map` of
`Ideal.quotientMap` applied to `φ`. -/
theorem adicStageMap_left {A B : Type u} [CommRing A] [CommRing B] {I : Ideal A}
    {J : Ideal B} (φ : A →+* B)
    (hpow : ∀ n : ℕ, I ^ (n + 1) ≤ (J ^ (n + 1)).comap φ) (n : ℕ)
    {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) :
    (adicStageMap φ hpow n hA).left =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap (J ^ (n + 1)) φ (hpow n))) :=
  sorry

/-- The quotient-induced stage maps commute with every transition of the canonical
power-thickening diagrams. -/
theorem adicStageMap_naturality {A B : Type u} [CommRing A] [CommRing B]
    {I : Ideal A} {J : Ideal B} (φ : A →+* B)
    (hpow : ∀ n : ℕ, I ^ (n + 1) ≤ (J ^ (n + 1)).comap φ) {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S) {m n : ℕ} (transitionHom : m ⟶ n) :
    (powerThickenings (Spec.map (CommRingCat.ofHom φ) ≫ hA) J).map transitionHom ≫
        adicStageMap φ hpow n hA =
      adicStageMap φ hpow m hA ≫ (powerThickenings hA I).map transitionHom :=
  sorry

/-- The morphism of thickening diagrams induced by `φ : A →+* B`. -/
def adicThickeningsMap {A B : Type u} [CommRing A] [CommRing B] {I : Ideal A}
    {J : Ideal B} (φ : A →+* B)
    (hpow : ∀ n : ℕ, I ^ (n + 1) ≤ (J ^ (n + 1)).comap φ) {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S) :
    powerThickenings (Spec.map (CommRingCat.ofHom φ) ≫ hA) J ⟶
      powerThickenings hA I :=
  { app := fun n ↦ adicStageMap φ hpow n hA
    naturality := fun _ _ transitionHom ↦ adicStageMap_naturality φ hpow hA transitionHom }

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
            (powerThickenings (Spec.map (CommRingCat.ofHom φ) ≫ hA) J) U ∧
          FormalAlgebraicSpace.IsDirectedAffineThickeningColimit
              (powerThickenings hA I) V ∧
            ∃ (cU : Cocone
                (powerThickenings (Spec.map (CommRingCat.ofHom φ) ≫ hA) J ⋙
                  yoneda))
              (cV : Cocone (powerThickenings hA I ⋙ yoneda))
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
                (powerThickenings (Spec.map (CommRingCat.ofHom φ) ≫ hA) J) U ∧
              FormalAlgebraicSpace.IsDirectedAffineThickeningColimit
                  (powerThickenings hA I) V ∧
                ∃ (cU : Cocone
                    (powerThickenings (Spec.map (CommRingCat.ofHom φ) ≫ hA) J ⋙
                      yoneda))
                  (cV : Cocone (powerThickenings hA I ⋙ yoneda))
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
          (powerThickenings hB J) U :=
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
          (powerThickenings hA I) V :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
