/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Family.EffectiveCartier
import StacksCheckRecall

@[expose] public section

universe u v

namespace AlgebraicGeometry.Scheme.Modules.AmpleFamily

/- Lemma 37.80.1: finitely many effective Cartier divisors with empty common support,
whose open complements carry ample restrictions of invertible modules, yield an ample family. -/
@[stacks 0GTS] #check
  (AlgebraicGeometry.Scheme.Modules.AmpleFamily.exists_of_effectiveCartierDivisors :
    ∀ {X : Scheme.{u}} {ι : Type v} [Finite ι]
      (D : ι → X.IdealSheafData) [∀ i, IsEffectiveCartierDivisor (D i).subschemeι]
      (L : ι → X.Modules) [∀ i, Invertible (L i)]
      [∀ i, IsAmple ((pullback (D i).openComplement.ι).obj (L i))]
      (_ : (⋂ i, ((D i).support : Set X)) = (∅ : Set X)),
      ∃ (κ : Type (max u v)) (M : κ → X.Modules), AmpleFamily M)

end AlgebraicGeometry.Scheme.Modules.AmpleFamily
