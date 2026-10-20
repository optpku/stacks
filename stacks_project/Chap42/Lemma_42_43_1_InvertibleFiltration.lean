module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Filtration.Invertible

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/- The prescribed-length filtration API is owned by the reusable filtration module. -/
#check (AlgebraicGeometry.Scheme.Modules.HasInvertibleQuotientFiltrationOfLength :
  ∀ {X : AlgebraicGeometry.Scheme.{u}}, ℕ → X.Modules → Prop)

#check (AlgebraicGeometry.Scheme.Modules.hasInvertibleQuotientFiltrationOfLength_iff :
  ∀ {X : AlgebraicGeometry.Scheme.{u}} (r : ℕ) (E : X.Modules),
    AlgebraicGeometry.Scheme.Modules.HasInvertibleQuotientFiltrationOfLength r E ↔
      ∃ s : RelSeries {FG : Subobject E × Subobject E |
          ∃ hFG : FG.1 ≤ FG.2,
            AlgebraicGeometry.Scheme.Modules.Invertible
              (cokernel (Subobject.ofLE FG.1 FG.2 hFG))},
        s.length = r ∧ s.head = ⊥ ∧ s.last = ⊤)

#check
  (AlgebraicGeometry.Scheme.Modules.HasInvertibleQuotientFiltrationOfLength.toHasInvertibleQuotientFiltration :
  ∀ {X : AlgebraicGeometry.Scheme.{u}} {r : ℕ} {E : X.Modules},
    AlgebraicGeometry.Scheme.Modules.HasInvertibleQuotientFiltrationOfLength r E →
      AlgebraicGeometry.Scheme.Modules.HasInvertibleQuotientFiltration E)
