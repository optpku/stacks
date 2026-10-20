module

public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ProjectiveSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ProjectiveSpace.Twist
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.RationalHilbert

/-!
# Hilbert Quot functors on projective space over the integers

Quotients of finite free sheaves on projective space with a fixed rational
Hilbert polynomial form a functor proper over `Spec(ℤ)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

/-- `Spec(ℤ)` viewed as an algebraic space over the terminal scheme. -/
abbrev specInt : AlgebraicSpace (⊤_ Scheme.{u}) :=
  ofOver (Over.mk (𝟙 (⊤_ Scheme.{u})))

/-- The structure morphism of projective space over `Spec(ℤ)` is of finite presentation. -/
instance instFinitePresentationProjectiveToSpec (n : ℕ) :
    FinitePresentation (ProjectiveSpace.toBase n specInt) := sorry

/-- The structure morphism of projective space over `Spec(ℤ)` is separated. -/
instance instSeparatedProjectiveToSpec (n : ℕ) :
    Separated (ProjectiveSpace.toBase n specInt) := sorry

/-- The finite free sheaf of rank `r` on projective space over `Spec(ℤ)` is quasi-coherent. -/
instance instIsQuasicoherentProjectiveFreeFin (n r : ℕ) :
    (SheafOfModules.freeFin r :
      (ProjectiveSpace n specInt).Modules).IsQuasicoherent := sorry

/-- The Hilbert Quot functor of quotients of `𝒪^{⊕ r}` on projective `n`-space
over `Spec(ℤ)` with rational Hilbert polynomial `P`, using the twist `𝒪(1)`. -/
abbrev quotHilbertProjective (n r : ℕ) (P : Polynomial ℚ) :=
  quotRationalHilbert (ProjectiveSpace.toBase n specInt)
    (SheafOfModules.freeFin r : (ProjectiveSpace n specInt).Modules)
    (ProjectiveSpace.twistingSheaf n specInt) P

/-- The Hilbert Quot functor of quotients of a positive-rank finite free sheaf
on projective space over `Spec(ℤ)` is proper for every rational Hilbert polynomial. -/
theorem quotHilbertProjective_isProperOver (n r : ℕ) (hr : 1 ≤ r) (P : Polynomial ℚ) :
    IsProperOver (quotHilbertProjective n r P).toFunctor := sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
