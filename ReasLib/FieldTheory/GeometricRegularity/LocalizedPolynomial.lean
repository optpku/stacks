module

public import ReasLib.FieldTheory.GeometricRegularity.Local
public import ReasLib.RingTheory.RingHom.Fiber.Map
public import ReasLib.RingTheory.RingHom.Local.AtPrime
import Mathlib.Tactic.CrossRefAttribute

/-!
# Localized polynomial approximations of geometrically regular local algebras

This leaf states the flatness and regular-closed-fiber consequences of a
differential basis carried by a finitely generated residue subextension.

@stack 07E6
-/

@[expose] public section

open IsLocalRing

noncomputable section

universe u v

namespace Algebra.IsGeometricallyRegular

/-- Lemma 15.35.2 (1), tag `07E6`: a localized
polynomial presentation whose residue coordinates form a differential basis
of a finitely generated subextension is flat over a geometrically regular
local algebra. -/
@[stacks 07E6 "(1)"]
theorem localizedPolynomial_map_flat
    {k : Type u} {A : Type v} [Field k] [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [Algebra k A] {p : ℕ} [Fact p.Prime] [CharP k p]
    [IsGeometricallyRegular k A] {m : ℕ}
    (phi : MvPolynomial (Fin m) k →ₐ[k] A)
    (F : IntermediateField k (ResidueField A)) (hF : F.FG)
    (y : Fin m → F)
    (hresidue : ∀ i, residue A (phi (MvPolynomial.X i)) =
      algebraMap F (ResidueField A) (y i))
    (hy : LinearIndependent F (KaehlerDifferential.D k F ∘ y))
    (hspan : Submodule.span F
      (Set.range (KaehlerDifferential.D k F ∘ y)) = ⊤) :
    (RingHom.LocalTarget.mapAtClosedPoint phi.toRingHom).Flat := sorry

/-- Lemma 15.35.2 (2), tag `07E6`: under the same
differential-basis hypotheses, the closed fiber of the localized polynomial
presentation is a regular local ring. -/
@[stacks 07E6 "(2)"]
theorem localizedPolynomial_closedFiber_regular
    {k : Type u} {A : Type v} [Field k] [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [Algebra k A] {p : ℕ} [Fact p.Prime] [CharP k p]
    [IsGeometricallyRegular k A] {m : ℕ}
    (phi : MvPolynomial (Fin m) k →ₐ[k] A)
    (F : IntermediateField k (ResidueField A)) (hF : F.FG)
    (y : Fin m → F)
    (hresidue : ∀ i, residue A (phi (MvPolynomial.X i)) =
      algebraMap F (ResidueField A) (y i))
    (hy : LinearIndependent F (KaehlerDifferential.D k F ∘ y))
    (hspan : Submodule.span F
      (Set.range (KaehlerDifferential.D k F ∘ y)) = ⊤) :
    IsRegularLocalRing
      ((RingHom.LocalTarget.mapAtClosedPoint phi.toRingHom).Fiber
        (maximalIdeal
          (Localization.AtPrime
            (Ideal.comap phi.toRingHom (maximalIdeal A))))) := sorry

end Algebra.IsGeometricallyRegular
