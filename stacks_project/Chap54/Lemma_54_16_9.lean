module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ExceptionalCurve.ContractionProjective
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.IsExceptionalCurveFirstKind

/- Lemma 54.16.9 (1): an exceptional curve of the first kind contained in a fibre of a
projective finite-type morphism to a Noetherian scheme admits a contraction whose target is
projective over the same base. -/
@[stacks 0C2N]
#check (AlgebraicGeometry.IsExceptionalCurveFirstKind.exists_projectiveContraction :
  ∀ {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S)
    [Scheme.Hom.FiniteType f] [Projective f]
    (E : X.IdealSheafData) [IsExceptionalCurveFirstKind E]
    (h_fiber : ∃ s : S, Set.MapsTo f E.support ({s} : Set S)),
    -- Local instance justification (proof-local temporary data): finite type over the
    -- Noetherian base canonically supplies `IsNoetherian X`, required by `IsContraction`.
    let _ : IsNoetherian X := Hom.FiniteType.isNoetherian f
    ∃ (X' : Scheme.{u}) (b : X ⟶ X') (x : closedPoints X') (f' : X' ⟶ S),
      IsContraction E b x ∧ b ≫ f' = f ∧ Projective f')

/- Lemma 54.16.9 (2): an exceptional curve of the first kind contained in a fibre of a
quasi-projective finite-type morphism to a Noetherian scheme admits a contraction whose target
is quasi-projective over the same base. -/
@[stacks 0C2N]
#check (AlgebraicGeometry.IsExceptionalCurveFirstKind.exists_quasiProjectiveContraction :
  ∀ {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S)
    [Scheme.Hom.FiniteType f] [QuasiProjective f]
    (E : X.IdealSheafData) [IsExceptionalCurveFirstKind E]
    (h_fiber : ∃ s : S, Set.MapsTo f E.support ({s} : Set S)),
    -- Local instance justification (proof-local temporary data): finite type over the
    -- Noetherian base canonically supplies `IsNoetherian X`, required by `IsContraction`.
    let _ : IsNoetherian X := Hom.FiniteType.isNoetherian f
    ∃ (X' : Scheme.{u}) (b : X ⟶ X') (x : closedPoints X') (f' : X' ⟶ S),
      IsContraction E b x ∧ b ≫ f' = f ∧ QuasiProjective f')

end AlgebraicGeometry.IsExceptionalCurveFirstKind
