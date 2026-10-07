module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactGeometricPairing
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactTwistedInput

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace AlgebraicGeometry.SchemeOverField.AmbientGeometry
variable {k : Type u} [Field k]
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
variable (X : SchemeOverField k)
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (ηbar : GeometricPoint (geometricBaseChange X))

/-- The explicit finite-fiber Galois comparison is bijective by the field's finite-étale classification. -/
theorem galoisPointComparison_bijective : Function.Bijective (galoisToGaloisPoint X ηbar) := sorry

/-- The arithmetic quotient to the actual Galois group uses the specified fiber comparison inverse. -/
def arithmeticGaloisQuotient :
    Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)) →* Gal(AlgebraicClosure k/k) :=
  (MulEquiv.ofBijective (galoisToGaloisPoint X ηbar)
    (galoisPointComparison_bijective X ηbar)).symm.toMonoidHom.comp
      (arithmeticToGalois X (arithmeticPoint X ηbar)).hom.toMonoidHom

/-- The actual arithmetic cyclotomic character is valued in coefficient units,
using ZMod(card Λ) → Λ rather than an arbitrary character or a natural-number cast. -/
def arithmeticCyclotomic (hΛ : IsUnit (Nat.card Λ : k)) :
    Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)) →* Λˣ :=
  (cyclotomicCharacterMod (Λ := Λ) k hΛ).comp (arithmeticGaloisQuotient X ηbar)

/-- This particular finite-level cyclotomic character has open kernel. -/
theorem arithmeticCyclotomic_openKernel (hΛ : IsUnit (Nat.card Λ : k)) :
    IsOpen ((arithmeticCyclotomic Λ X ηbar hΛ).ker :
      Set (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))) := sorry

/-- The actual cyclotomic character is trivial on geometric π₁ by the exact sequence. -/
theorem arithmeticCyclotomic_geometric (hΛ : IsUnit (Nat.card Λ : k))
    (g : Aut (standardFiniteEtaleFiber ηbar)) :
    arithmeticCyclotomic Λ X ηbar hΛ (geometricToArithmetic X ηbar g) = 1 := sorry

/-- The inverse Tate coefficient specializes Kuhn's explicit twist to the actual arithmetic character. -/
def arithmeticInverseTate (hΛ : IsUnit (Nat.card Λ : k))
    (M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))) :=
  CompactRepresentation.inverseCharacterTwist Λ
    (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))
    (arithmeticCyclotomic Λ X ηbar hΛ) (arithmeticCyclotomic_openKernel Λ X ηbar hΛ) M

/-- The specialized inverse Tate action is exactly inverse-cyclotomic scalar multiplication. -/
theorem arithmeticInverseTate_action (hΛ : IsUnit (Nat.card Λ : k))
    (M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar))))
    (g : Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar))) (m : M.obj.V) :
    ((arithmeticInverseTate Λ X ηbar hΛ M).obj.ρ g).hom m =
      (((arithmeticCyclotomic Λ X ηbar hΛ g)⁻¹ : Λˣ) : Λ) • (M.obj.ρ g).hom m := rfl

/-- Actual geometric restriction of the inverse-Tate coefficient. -/
def geometricInverseTate (hΛ : IsUnit (Nat.card Λ : k))
    (M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))) :=
  geometricRestriction X ηbar (arithmeticInverseTate Λ X ηbar hΛ M)

/-- Finiteness is retained because the actual inverse twist and restriction keep the carrier. -/
instance geometricInverseTate_finite (hΛ : IsUnit (Nat.card Λ : k))
    (M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar))))
    [Finite M.obj.V] : Finite (geometricInverseTate Λ X ηbar hΛ M).obj.V :=
  inferInstanceAs (Finite M.obj.V)

end AlgebraicGeometry.SchemeOverField.AmbientGeometry
