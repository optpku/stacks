module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.Parameters
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.Perturbation.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.DifferenceConstruction

/-!
# Recovering the parameter of an actual infinitesimal automorphism section

The first-order base is itself thickened: the derivation is relative to `U`, whereas
the ambient section lies over `U'`. Local surjectivity of the base restriction makes the
actual difference derivation annihilate the `U` coefficients. Its function is still the
specified conormal difference and sheaf descent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

variable {S : Scheme.{u}} {U U' I I' : AlgebraicSpace S}
variable (iU : U ⟶ U') (iI : I ⟶ I') (p' : I' ⟶ U') (p : I ⟶ U)
variable (Δ' : U' ⟶ I') (Δ : U ⟶ I)
variable [IsFirstOrderThickening iU] [IsFirstOrderThickening iI]
variable (hΔ : IsPullback Δ iU iI Δ') (hp : IsPullback p iI iU p')
variable (hsec : Δ' ≫ p' = 𝟙 U')

/-- An actual identity-chart section has the prescribed reduction and source projection. -/
def IdentitySection :=
  { δ : U' ⟶ I' // iU ≫ δ = Δ ≫ iI ∧ δ ≫ p' = 𝟙 U' }

/-- The section's reduction is the commutative square used by the conormal construction. -/
theorem identitySectionSquare (δ : IdentitySection iU iI p' Δ) :
    CommSq Δ iU iI δ.val :=
  ⟨δ.property.1.symm⟩

include hp hsec in
/-- In a cartesian first-order diagram, a section over `U'` induces the same conormal
comparison as the diagonal. This uses its actual reduction and source projection. -/
private theorem identitySection_conormal (δ : IdentitySection iU iI p' Δ) :
    Hom.Conormal.map hΔ.toCommSq = Hom.Conormal.map (identitySectionSquare iU iI p' Δ δ) :=
  sorry

/-- The actual additive section map recovered from the diagonal minus the supplied section. -/
def identitySectionDifference (δ : IdentitySection iU iI p' Δ) :
    (sheafCompose (smallEtaleTopology I) (forget₂ RingCat AddCommGrpCat.{u})).obj
        (structureSheaf I) ⟶
      (SheafOfModules.toSheaf (structureSheaf I)).obj
        ((Modules.pushforward Δ).obj (Hom.conormalSheaf iU)) :=
  differenceAdjoint iU iI Δ Δ' δ.val hΔ.toCommSq (identitySectionSquare iU iI p' Δ δ)
    (by exact identitySection_conormal iU iI p' p Δ' Δ hΔ hp hsec δ)

/-- The diagonal-minus-section functions obey the Leibniz and restriction laws
and vanish on the coefficients from the reduced base. -/
private theorem identitySectionDerivation_laws (δ : IdentitySection iU iI p' Δ) :
    let M := toCommPresheaf ((Modules.pushforward Δ).obj (Hom.conormalSheaf iU))
    let d : ∀ T : (smallEtaleSite I)ᵒᵖ,
        (commStructureSheaf I).obj.obj T →+ M.obj T := fun T ↦
      (identitySectionDifference iU iI p' p Δ' Δ hΔ hp hsec δ).hom.app T |>.hom
    (∀ T (a b : (commStructureSheaf I).obj.obj T),
      d T (a * b) = a • d T b + b • d T a) ∧
    (∀ {T V : (smallEtaleSite I)ᵒᵖ} (f : T ⟶ V)
      (a : (commStructureSheaf I).obj.obj T),
      d V ((commStructureSheaf I).obj.map f a) = M.map f (d T a)) ∧
    (∀ T (a : (commInverseImageStructureSheaf p).obj.obj T),
      d T ((commInverseImageStructureSheafMap p).hom.app T a) = 0) := sorry

/-- The ordered sectionwise difference is a derivation relative to the reduced base. -/
def identitySectionDerivation (δ : IdentitySection iU iI p' Δ) :
    Hom.derivations p ((Modules.pushforward Δ).obj (Hom.conormalSheaf iU)) where
  d {T} := (identitySectionDifference iU iI p' p Δ' Δ hΔ hp hsec δ).hom.app T |>.hom
  d_mul {T} a b := by exact (identitySectionDerivation_laws iU iI p' p Δ' Δ hΔ hp hsec δ).1 T a b
  d_map {T V} f a := by exact (identitySectionDerivation_laws iU iI p' p Δ' Δ hΔ hp hsec δ).2.1 f a
  d_app {T} a := by exact (identitySectionDerivation_laws iU iI p' p Δ' Δ hΔ hp hsec δ).2.2 T a

/-- Recover the differential parameter by universal descent and the pullback–pushforward
adjunction. -/
def identitySectionParameter (δ : IdentitySection iU iI p' Δ) :
    (Modules.pullback Δ).obj (Hom.relativeDifferentials p) ⟶ Hom.conormalSheaf iU :=
  ((Modules.pullbackPushforwardAdjunction Δ).homEquiv _ _).symm
    (SheafOfModules.RingedSite.relativeDifferentialDesc
      (commInverseImageStructureSheafMap p)
      (identitySectionDerivation iU iI p' p Δ' Δ hΔ hp hsec δ))

/-- The recovered derivation is exactly the original diagonal-minus-section difference. -/
theorem identitySectionDerivation_spec (δ : IdentitySection iU iI p' Δ) :
    structureMapDifference_restrict iU iI Δ Δ' δ.val hΔ.toCommSq.w.symm
        (identitySectionSquare iU iI p' Δ δ).w.symm =
      factorizationMap p iU iI Δ
        (identitySectionDerivation iU iI p' p Δ' Δ hΔ hp hsec δ) := sorry

/-- The parameter's canonical derivation has the specified section functions. -/
theorem identitySectionParameter_derivation (δ : IdentitySection iU iI p' Δ) :
    Hom.derivationOfPullback p Δ
        (identitySectionParameter iU iI p' p Δ' Δ hΔ hp hsec δ) =
      identitySectionDerivation iU iI p' p Δ' Δ hΔ hp hsec δ := sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

variable {S : Scheme.{u}} {U U' I I' : AlgebraicSpace S}
variable (iU : U ⟶ U') (iI : I ⟶ I') (p' : I' ⟶ U') (p : I ⟶ U)
variable (Δ' : U' ⟶ I') (Δ : U ⟶ I)
variable [IsFirstOrderThickening iU] [IsFirstOrderThickening iI]
variable (hΔ : IsPullback Δ iU iI Δ') (hp : IsPullback p iI iU p')
variable (hsec : Δ' ≫ p' = 𝟙 U')
variable (θ : (Modules.pullback Δ).obj (Hom.relativeDifferentials p) ⟶ Hom.conormalSheaf iU)

/-- The actual diagonal perturbation has the original reduced map. -/
theorem diagonalPerturbation_restrict :
    iU ≫ perturbHom iU iI Δ Δ' hΔ.toCommSq p θ = Δ ≫ iI := sorry

include hp hsec in
/-- Since the parameter is relative to `I -> U`, its perturbation remains a section of
the ambient projection `I' -> U'`. -/
theorem diagonalPerturbation_source :
    perturbHom iU iI Δ Δ' hΔ.toCommSq p θ ≫ p' = 𝟙 U' := sorry

/-- Act on the actual diagonal using the actual scheme-chart perturbation and gluing. -/
def parameterIdentitySection : IdentitySection iU iI p' Δ :=
  ⟨perturbHom iU iI Δ Δ' hΔ.toCommSq p θ,
    diagonalPerturbation_restrict iU iI p Δ' Δ hΔ θ,
    diagonalPerturbation_source iU iI p' p Δ' Δ hΔ hp hsec θ⟩

/-- The forward section map retains exactly the constructed global perturbation. -/
theorem parameterIdentitySection_val :
    (parameterIdentitySection iU iI p' p Δ' Δ hΔ hp hsec θ).val =
      perturbHom iU iI Δ Δ' hΔ.toCommSq p θ := rfl

/-- Recovering the ordered difference of the parameter's perturbation gives that parameter. -/
theorem identitySectionParameter_parameterIdentitySection :
    identitySectionParameter iU iI p' p Δ' Δ hΔ hp hsec
        (parameterIdentitySection iU iI p' p Δ' Δ hΔ hp hsec θ) = θ := sorry

/-- Acting by the recovered difference parameter returns the original actual section. -/
theorem parameterIdentitySection_identitySectionParameter
    (δ : IdentitySection iU iI p' Δ) :
    parameterIdentitySection iU iI p' p Δ' Δ hΔ hp hsec
        (identitySectionParameter iU iI p' p Δ' Δ hΔ hp hsec δ) = δ := sorry

/-- Both directions of the global Hom-parameter/identity-section correspondence are actual
maps: common-atlas perturbation and ordered-difference descent. -/
def parameterIdentitySectionEquiv :
    ((Modules.pullback Δ).obj (Hom.relativeDifferentials p) ⟶ Hom.conormalSheaf iU) ≃
      IdentitySection iU iI p' Δ where
  toFun := parameterIdentitySection iU iI p' p Δ' Δ hΔ hp hsec
  invFun := identitySectionParameter iU iI p' p Δ' Δ hΔ hp hsec
  left_inv := identitySectionParameter_parameterIdentitySection iU iI p' p Δ' Δ hΔ hp hsec
  right_inv := parameterIdentitySection_identitySectionParameter iU iI p' p Δ' Δ hΔ hp hsec

end AlgebraicGeometry.AlgebraicSpace.Hom.Deformation
