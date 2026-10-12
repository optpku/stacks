/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ExceptionalCurve.ContractionPicard
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.IsExceptionalCurveFirstKind

/-- An exceptional curve of the first kind on a proper scheme over an affine Noetherian
base admits a contraction proper over that base, along which an ample invertible module
descends to an ample invertible module. -/
theorem exists_ampleContraction
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ] [Scheme.Modules.IsAmple ℒ]
    (E : X.IdealSheafData) [IsExceptionalCurveFirstKind E] :
    -- Local instance justification (proof-local temporary data): properness over the Noetherian base supplies the source Noetherian structure required by the contraction and descent predicates.
    let _ : IsNoetherian X :=
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
        toCompactSpace := (quasiCompact_iff_compactSpace f).mp inferInstance }
    ∃ (X' : Scheme.{u}) (b : X ⟶ X') (x : closedPoints X')
      (f' : X' ⟶ Spec (.of R)) (hb : IsContraction E b x),
      b ≫ f' = f ∧ IsProper f' ∧
        Scheme.Modules.IsAmple
          (hL := descendedModule_invertible E b x hb (Scheme.Modules.picardClass ℒ))
          (descendedModule E b x hb (Scheme.Modules.picardClass ℒ)) := sorry

end AlgebraicGeometry.IsExceptionalCurveFirstKind
