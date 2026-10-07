module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ExceptionalCurve.ContractionAmple
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.IsExceptionalCurveFirstKind

/- Lemma 54.16.8: an ample invertible module on a proper scheme over an affine Noetherian
scheme descends as an ample module after contracting an exceptional curve of the first kind. -/
@[stacks 0C2M]
#check (AlgebraicGeometry.IsExceptionalCurveFirstKind.exists_ampleContraction :
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ] [Scheme.Modules.IsAmple ℒ]
    (E : X.IdealSheafData) [IsExceptionalCurveFirstKind E],
    -- Local instance justification (proof-local temporary data): properness over the Noetherian base supplies the source Noetherian structure required by the contraction and descent predicates.
    let _ : IsNoetherian X :=
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
        toCompactSpace := (quasiCompact_iff_compactSpace f).mp inferInstance }
    ∃ (X' : Scheme.{u}) (b : X ⟶ X') (x : closedPoints X')
      (f' : X' ⟶ Spec (.of R)) (hb : IsContraction E b x),
      b ≫ f' = f ∧ IsProper f' ∧
        Scheme.Modules.IsAmple
          (hL := descendedModule_invertible E b x hb (Scheme.Modules.picardClass ℒ))
          (descendedModule E b x hb (Scheme.Modules.picardClass ℒ)))

end AlgebraicGeometry.IsExceptionalCurveFirstKind
