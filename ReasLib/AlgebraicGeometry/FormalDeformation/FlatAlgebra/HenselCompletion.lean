module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.Henselization
public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.AdicCompletion
public import ReasLib.RingTheory.Henselian.Pair.Completion
public import Mathlib.RingTheory.AdicCompletion.LocalRing

/-!
# Local henselization and completion of algebra deformations

Local henselization preserves the Artinian base. Completing along the
extended maximal ideal and transporting the residue ring gives the canonical
comparison with deformations of the completed local ring.
-/

@[expose] public section

open CategoryTheory Functor IsLocalRing RingPairCat
open scoped BasedFunctor

universe u

noncomputable section

namespace FlatAlgebraCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable [henselianPairInclusion.IsRightAdjoint]
variable (P : Type u) [CommRing P] [Algebra k P] [IsLocalRing P] [IsNoetherianRing P]

/-- Pair henselization of deformations commutes with forgetting to `C_Λ`. -/
theorem henselizationLocalFunctor_comp_forget :
    henselizationFunctor Λ k P (maximalIdeal P) ⋙
        deformationForget Λ k (henselizationRing (pairOfIdeal (maximalIdeal P)) : Type u) =
      deformationForget Λ k P :=
  sorry

/-- The functor `Def_P ⟶ Def_{P^h}` as a morphism of categories over `C_Λ`. -/
def henselizationLocalBasedFunctor :
    BasedCategory.ofFunctor (deformationForget Λ k P) ⥤ᵇ
      BasedCategory.ofFunctor
        (deformationForget Λ k (henselizationRing (pairOfIdeal (maximalIdeal P)) : Type u)) where
  toFunctor := henselizationFunctor Λ k P (maximalIdeal P)
  w := henselizationLocalFunctor_comp_forget Λ k P

/-- Pair henselization of a Noetherian local ring remains Noetherian. -/
instance instIsNoetherianRing_henselizationRing_maximalIdeal :
    IsNoetherianRing (henselizationRing (pairOfIdeal (maximalIdeal P)) : Type u) :=
  @henselizationRing_isNoetherian (pairOfIdeal (maximalIdeal P))
    (inferInstanceAs (IsNoetherianRing P)) _

/-- The extended maximal ideal of a local ring in its henselization. -/
def henselExtendedMaximalIdealOf :
    Ideal (henselizationRing (pairOfIdeal (maximalIdeal P)) : Type u) :=
  Ideal.map (toHenselization (pairOfIdeal (maximalIdeal P))) (maximalIdeal P)


end FlatAlgebraCat

namespace FlatAlgebraCat

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- An algebra map between residue rings commutes with the identity base map. -/
theorem residueTransportHom_commutes {R S : Type u} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (φ : R →ₐ[k] S) :
    φ.toRingHom.comp
        (algebraMap (ofResidue Λ k R).base.carrier (ofResidue Λ k R).algebra) =
      (algebraMap (ofResidue Λ k S).base.carrier (ofResidue Λ k S).algebra).comp
        (𝟙 (ofResidue Λ k R).base : (ofResidue Λ k R).base ⟶
          (ofResidue Λ k S).base).hom.toRingHom := sorry

/-- A bijective algebra map between residue rings has bijective canonical tensor lift. -/
theorem residueTransportHom_isIsoTensor {R S : Type u} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (φ : R →ₐ[k] S) (hφ : Function.Bijective φ.toRingHom) :
    Function.Bijective (canonicalTensorMap
      (Q := ofResidue Λ k R) (P := ofResidue Λ k S)
      (𝟙 (ofResidue Λ k R).base) φ.toRingHom
      (residueTransportHom_commutes (Λ := Λ) φ)) := sorry

variable (Λ k) in
/-- A specified bijective residue algebra map defines a flat-algebra morphism over the identity base. -/
def residueTransportHom {R S : Type u} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (φ : R →ₐ[k] S) (hφ : Function.Bijective φ.toRingHom) :
    ofResidue Λ k R ⟶ ofResidue Λ k S :=
  Hom.of (𝟙 (ofResidue Λ k R).base) φ.toRingHom
    (residueTransportHom_commutes (Λ := Λ) φ)
    (residueTransportHom_isIsoTensor (Λ := Λ) φ hφ)

variable (Λ k) in
/-- Postcompose the residue of a deformation along a bijective `k`-algebra map of
residue rings, keeping the same Artinian local base. -/
def deformationResidueTransport {R S : Type u} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (φ : R →ₐ[k] S) (hφ : Function.Bijective φ.toRingHom) :
    deformationCategory Λ k R ⥤ deformationCategory Λ k S where
  obj ξ := Over.mk (ξ.hom ≫ residueTransportHom Λ k φ hφ)
  map g := Over.homMk g.left sorry
  map_id := sorry
  map_comp := sorry

variable (Λ k) in
/-- Residue transport does not change the Artinian local base. -/
theorem deformationResidueTransport_obj_base {R S : Type u} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (φ : R →ₐ[k] S) (hφ : Function.Bijective φ.toRingHom)
    (ξ : deformationCategory Λ k R) :
    ((deformationResidueTransport Λ k φ hφ).obj ξ).left.base = ξ.left.base :=
  rfl

end FlatAlgebraCat

namespace FlatAlgebraCat

variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable [henselianPairInclusion.IsRightAdjoint]

variable (P : Type u) [CommRing P] [IsLocalRing P] [IsNoetherianRing P]

/-- Pair henselization followed by `henselizationToAdicCompletion` is the
canonical map into the adic completion. -/
private theorem henselizationToAdicCompletion_comp_toHenselization
    (X : RingPairCat.{u}) [IsNoetherianRing X.ring] :
    (henselizationToAdicCompletion X).comp (toHenselization X) =
      algebraMap X.ring (AdicCompletion X.ideal X.ring) :=
  congrArg ringHom
    (((Adjunction.ofIsRightAdjoint henselianPairInclusion).homEquiv X
        ⟨adicCompletionPair X, adicCompletion_henselian X⟩).apply_symm_apply
      (toAdicCompletionPair X))

/-- Completing `P^h` along the extended maximal ideal is adically continuous
toward the maximal ideal of `P^∧`. -/
private theorem henselizationToCompleteAdicContinuous :
    (@henselizationToAdicCompletion (pairOfIdeal (maximalIdeal P))
      (inferInstanceAs (IsNoetherianRing P)) _).AdicContinuous
      (henselExtendedMaximalIdealOf P)
      (maximalIdeal (AdicCompletion (maximalIdeal P) P)) :=
  ⟨1, (pow_one (henselExtendedMaximalIdealOf P)).symm ▸
    le_of_eq
      ((Ideal.map_map (toHenselization (pairOfIdeal (maximalIdeal P)))
          (@henselizationToAdicCompletion (pairOfIdeal (maximalIdeal P))
            (inferInstanceAs (IsNoetherianRing P)) _)).trans
        ((congrArg (fun φ ↦ Ideal.map φ (maximalIdeal P))
            (@henselizationToAdicCompletion_comp_toHenselization _
              (pairOfIdeal (maximalIdeal P)) (inferInstanceAs (IsNoetherianRing P)))).trans
          (AdicCompletion.maximalIdeal_eq_map (R := P)).symm))⟩


/-- The completion of `P^h` along the extended maximal ideal. -/
abbrev henselCompleteRing (P : Type u) [CommRing P] [IsLocalRing P] : Type u :=
  AdicCompletion (henselExtendedMaximalIdealOf P)
    (henselizationRing (pairOfIdeal (maximalIdeal P)) : Type u)

/-- Comparison `(P^h)^∧ →ₐ[k] P^∧` induced by pair henselization. -/
def henselCompletionToComplete (k : Type u) [Field k] (P : Type u)
    [CommRing P] [Algebra k P] [IsLocalRing P] [IsNoetherianRing P] :
    henselCompleteRing P →ₐ[k] AdicCompletion (maximalIdeal P) P where
  toRingHom :=
    (AdicCompletion.ofAlgEquiv
        (maximalIdeal (AdicCompletion (maximalIdeal P) P))).symm.toRingHom.comp
      (RingHom.AdicContinuous.completionMap
        (f := @henselizationToAdicCompletion (pairOfIdeal (maximalIdeal P))
          (inferInstanceAs (IsNoetherianRing P)) _)
        (by exact henselizationToCompleteAdicContinuous P))
  commutes' := sorry

/-- Completing the henselization recovers the completion of the local ring. -/
theorem henselCompletionToComplete_bijective (k : Type u) [Field k] (P : Type u)
    [CommRing P] [Algebra k P] [IsLocalRing P] [IsNoetherianRing P] :
    Function.Bijective (henselCompletionToComplete k P).toRingHom :=
  sorry

/-- Completing the henselization and transporting the residue ring preserves the
projection to the Artinian local base. -/
theorem completionFromHenselLocalFunctor_comp_forget (Λ k : Type u)
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (P : Type u) [CommRing P] [Algebra k P] [IsLocalRing P] [IsNoetherianRing P] :
    Functor.comp (adicCompletionFunctor Λ k
      (henselizationRing (pairOfIdeal (maximalIdeal P)) : Type u)
      (henselExtendedMaximalIdealOf P))
      (deformationResidueTransport Λ k (henselCompletionToComplete k P)
        (henselCompletionToComplete_bijective k P)) ⋙
        deformationForget Λ k (AdicCompletion (maximalIdeal P) P) =
      deformationForget Λ k (henselizationRing (pairOfIdeal (maximalIdeal P)) : Type u) :=
  sorry

/-- The based functor `Def_{P^h} ⥤ᵇ Def_{P^∧}` for a Noetherian local `k`-algebra,
completing along the extended maximal ideal and transporting the residue ring along
`henselizationToAdicCompletion`. -/
def completionFromHenselLocalBasedFunctor (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ]
    [Field k] [Algebra Λ k] [Module.Finite Λ k] (P : Type u)
    [CommRing P] [Algebra k P] [IsLocalRing P] [IsNoetherianRing P] :
    BasedCategory.ofFunctor
        (deformationForget Λ k (henselizationRing (pairOfIdeal (maximalIdeal P)) : Type u)) ⥤ᵇ
      BasedCategory.ofFunctor (deformationForget Λ k (AdicCompletion (maximalIdeal P) P)) where
  toFunctor :=
    Functor.comp (adicCompletionFunctor Λ k
      (henselizationRing (pairOfIdeal (maximalIdeal P)) : Type u)
      (henselExtendedMaximalIdealOf P))
      (deformationResidueTransport Λ k (henselCompletionToComplete k P)
        (henselCompletionToComplete_bijective k P))
  w := completionFromHenselLocalFunctor_comp_forget Λ k P

end FlatAlgebraCat

end
