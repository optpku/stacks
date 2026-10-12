/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Group.Differentials
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Differentials
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.GroupScheme

/-- A locally algebraic group scheme over a characteristic-zero field has smooth structure
morphism. -/
instance instSmoothOfCharZero {k : Type u} [Field k] [CharZero k]
    (G : SchemeOverField k) [GrpObj G] [LocallyAlgebraic G] : Smooth G.hom := sorry

/-- A reduced locally algebraic group scheme over a perfect field of prime characteristic has
smooth structure morphism. -/
instance instSmoothOfPerfectFieldOfIsReduced {p : ℕ} [Fact p.Prime]
    {k : Type u} [Field k] [CharP k p] [PerfectField k]
    (G : SchemeOverField k) [GrpObj G] [LocallyAlgebraic G] [IsReduced G.left] :
    Smooth G.hom := by
  have h_locallyFree : (Ω[G.hom.toShHom]).IsLocallyFree := by
    rcases SheafOfModules.IsFree.exists_iso_free (F := Ω[G.hom.toShHom]) with ⟨I, ⟨e⟩⟩
    exact SheafOfModules.IsLocallyFree.of_iso e.symm
  -- Local instance justification (proof-local temporary data): the smoothness criterion is
  -- class-based, and this proof needs locally free differentials only for this inference step.
  let _ : (Ω[G.hom.toShHom]).IsLocallyFree := h_locallyFree
  exact inferInstance

end AlgebraicGeometry.GroupScheme
