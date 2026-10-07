module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectDerived.Representability
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 57.6.4: if `X` is proper and regular over a field `k`, every `k`-linear
homological functor on `PerfectDerived X` whose values on all shifts have finite total
dimension is corepresented by a perfect complex. -/
@[stacks 0H4A]
#check
  (AlgebraicGeometry.SchemeOverField.PerfectDerived.existsPerfectCorepresentation :
    {k : Type u} → [Field k] → (X : SchemeOverField k) → [IsProper X.hom] →
    [Scheme.Regular X.left] →
    (G : SchemeOverField.PerfectDerived X ⥤ ModuleCat k) →
    [G.IsHomological] → [G.Linear k] →
    (hG_finite : ∀ E : SchemeOverField.PerfectDerived X,
      GradedObject.FiniteTotalDimension (fun n : ℤ ↦ G.obj (E⟦n⟧))) →
    ∃ K : SchemeOverField.PerfectDerived X,
      Nonempty
        ((linearCoyoneda k (SchemeOverField.PerfectDerived X)).obj (Opposite.op K) ≅ G))

end
