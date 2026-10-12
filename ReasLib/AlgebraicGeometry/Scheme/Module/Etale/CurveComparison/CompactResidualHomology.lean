/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactResolution

@[expose] public section
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u

namespace CompactResidualHomology
variable (Λ G Γ Q : Type u) [CommRing Λ] [Finite Λ]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
variable [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [T2Space Q]
variable (φ : G →ₜ* Γ) (ψ : Γ →ₜ* Q)

/-- Actual restriction of a compact arithmetic action along the geometric group map. -/
def restrict (M : CompactRepresentation.Cat Λ Γ) : CompactRepresentation.Cat Λ G :=
  ⟨(Action.res (CompactModule Λ) φ.toMonoidHom).obj M.obj, sorry⟩

/-- Restriction keeps the actual continuous linear coefficient map. -/
def restrictFunctor : CompactRepresentation.Cat Λ Γ ⥤ CompactRepresentation.Cat Λ G where
  obj := restrict Λ G Γ φ
  map a := ObjectProperty.homMk ((Action.res (CompactModule Λ) φ.toMonoidHom).map a.hom)
  map_id := sorry
  map_comp := sorry

/-- The underlying residual module is the genuine quotient by CLOSED geometric relations. -/
def quotient (M : CompactRepresentation.Cat Λ Γ) : CompactModule Λ :=
  CompactRepresentation.coinvariants Λ G (restrict Λ G Γ φ M)

variable (hexact : MonoidHom.range φ.toMonoidHom = MonoidHom.ker ψ.toMonoidHom)

include hexact

/-- Arithmetic translates preserve the closed geometric relation module by normality of ker ψ. -/
theorem relations_stable (M : CompactRepresentation.Cat Λ Γ) (γ : Γ) :
    CompactRepresentation.relations Λ G (restrict Λ G Γ φ M) ≤
      (CompactRepresentation.relations Λ G (restrict Λ G Γ φ M)).comap
        (CompactModule.linear Λ (M.obj.ρ γ)) := sorry

/-- The arithmetic action descends by applying the actual continuous linear map to quotient representatives. -/
def arithmeticEnd (M : CompactRepresentation.Cat Λ Γ) (γ : Γ) :
    quotient Λ G Γ φ M ⟶ quotient Λ G Γ φ M :=
  { toLinearMap := (CompactRepresentation.relations Λ G (restrict Λ G Γ φ M)).mapQ
      (CompactRepresentation.relations Λ G (restrict Λ G Γ φ M))
      (CompactModule.linear Λ (M.obj.ρ γ)) (relations_stable Λ G Γ Q φ ψ hexact M γ)
    cont := sorry }

/-- Arithmetic elements with the same quotient image induce the same actual quotient map. -/
theorem arithmeticEnd_independent (M : CompactRepresentation.Cat Λ Γ)
    (γ δ : Γ) (h : ψ γ = ψ δ) :
    arithmeticEnd Λ G Γ Q φ ψ hexact M γ = arithmeticEnd Λ G Γ Q φ ψ hexact M δ := sorry

variable (hsurj : Function.Surjective ψ)

/-- A representative of a quotient element chosen through the given surjective homomorphism. -/
def lift (q : Q) : Γ := Function.surjInv hsurj q

/-- The selected representative has precisely the prescribed quotient image. -/
theorem lift_spec (q : Q) : ψ (lift Γ Q ψ hsurj q) = q := sorry

/-- The quotient-group action is built from arithmetic translates of representatives,
not by transporting through any group/geometric cohomology comparison. -/
def action (M : CompactRepresentation.Cat Λ Γ) : Action (CompactModule Λ) Q where
  V := quotient Λ G Γ φ M
  ρ := { toFun := fun q ↦ arithmeticEnd Λ G Γ Q φ ψ hexact M (lift Γ Q ψ hsurj q)
         map_one' := sorry
         map_mul' := sorry }

/-- The actual residual action is jointly continuous by the compact quotient topology. -/
theorem action_continuous (M : CompactRepresentation.Cat Λ Γ) :
    CompactRepresentation.continuousAction Λ Q (action Λ G Γ Q φ ψ hexact hsurj M) := sorry

/-- The genuine compact residual representation of geometric coinvariants. -/
def obj (M : CompactRepresentation.Cat Λ Γ) : CompactRepresentation.Cat Λ Q :=
  ⟨action Λ G Γ Q φ ψ hexact hsurj M, action_continuous Λ G Γ Q φ ψ hexact hsurj M⟩

/-- Residual coinvariants are functorial through the actual closed-quotient map. -/
def functor : CompactRepresentation.Cat Λ Γ ⥤ CompactRepresentation.Cat Λ Q where
  obj := obj Λ G Γ Q φ ψ hexact hsurj
  map a := ObjectProperty.homMk
    { hom := CompactRepresentation.coinvariantsMap Λ G ((restrictFunctor Λ G Γ φ).map a)
      comm := fun _ ↦ sorry }
  map_id := sorry
  map_comp := sorry

/-- Residual closed coinvariants are additive. -/
instance functor_additive : (functor Λ G Γ Q φ ψ hexact hsurj).Additive := sorry

/-- Residual closed coinvariants preserve finite colimits. -/
instance functor_preservesFiniteColimits :
    PreservesFiniteColimits (functor Λ G Γ Q φ ψ hexact hsurj) := sorry

/-- Higher residual homology is derived in compact arithmetic representations,
so its quotient-group action is already part of the actual derived-functor output. -/
def homology (n : ℕ) : CompactRepresentation.Cat Λ Γ ⥤ CompactRepresentation.Cat Λ Q :=
  (functor Λ G Γ Q φ ψ hexact hsurj).leftDerived n

/-- The canonical degree-zero derived comparison preserves the actual residual quotient action. -/
def zeroIso : homology Λ G Γ Q φ ψ hexact hsurj 0 ≅ functor Λ G Γ Q φ ψ hexact hsurj :=
  (functor Λ G Γ Q φ ψ hexact hsurj).leftDerivedZeroIsoSelf

/-- Any specified compact projective resolution computes the actual residual homology functor. -/
def resolutionIso (M : CompactRepresentation.Cat Λ Γ) (P : ProjectiveResolution M) (n : ℕ) :
    (homology Λ G Γ Q φ ψ hexact hsurj n).obj M ≅
      (HomologicalComplex.homologyFunctor (CompactRepresentation.Cat Λ Q) (ComplexShape.down ℕ) n).obj
        (((functor Λ G Γ Q φ ψ hexact hsurj).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) :=
  P.isoLeftDerivedObj (functor Λ G Γ Q φ ψ hexact hsurj) n

end CompactResidualHomology
