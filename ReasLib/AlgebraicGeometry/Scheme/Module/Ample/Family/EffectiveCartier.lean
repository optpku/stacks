/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.OpenComplement
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Family
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback

@[expose] public section

universe u v

namespace AlgebraicGeometry.Scheme.Modules.AmpleFamily

/-- Finitely many effective Cartier divisors with empty common support, whose open
complements carry ample restrictions of invertible modules, yield an ample family. -/
theorem exists_of_effectiveCartierDivisors {X : Scheme.{u}} {ι : Type v} [Finite ι]
    (D : ι → X.IdealSheafData) [∀ i, IsEffectiveCartierDivisor (D i).subschemeι]
    (L : ι → X.Modules) [∀ i, Invertible (L i)]
    [∀ i, IsAmple ((pullback (D i).openComplement.ι).obj (L i))]
    (h_inter : (⋂ i, ((D i).support : Set X)) = (∅ : Set X)) :
    ∃ (κ : Type (max u v)) (M : κ → X.Modules), AmpleFamily M := sorry

end AlgebraicGeometry.Scheme.Modules.AmpleFamily
