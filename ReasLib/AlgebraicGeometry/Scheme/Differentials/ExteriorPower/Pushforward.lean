module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.ExteriorPower.BaseChange

/-!
# Pushforward of relative differential forms

The pushforward-side adjoint of the comparison on relative differential forms associated to a
commutative square of schemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeDifferentials

variable {X' X S' S : Scheme.{u}}
variable {f : X' ⟶ X} {g : S' ⟶ S} {h : X ⟶ S} {h' : X' ⟶ S'}

/-- The pushforward-side adjoint of the comparison on relative differential forms associated
to a commutative square of schemes. -/
noncomputable def pushforwardComparison (sq : CommSq f h' h g) (a : ℕ) :
    (Λ[a] Ω[h.toShHom]) ⟶
      (RingedSpace.Hom.pushforward f.toShHom).obj (Λ[a] Ω[h'.toShHom]) :=
  (RingedSpace.Hom.pullbackPushforwardAdjunction f.toShHom).homEquiv _ _
    (formComparison sq a)

/-- Transposing `pushforwardComparison` back through pullback-pushforward adjunction recovers
the canonical comparison on relative differential forms. -/
theorem pushforwardComparison_adj (sq : CommSq f h' h g) (a : ℕ) :
    ((RingedSpace.Hom.pullbackPushforwardAdjunction f.toShHom).homEquiv _ _).symm
      (pushforwardComparison sq a) = formComparison sq a := sorry

end AlgebraicGeometry.Scheme.RelativeDifferentials
