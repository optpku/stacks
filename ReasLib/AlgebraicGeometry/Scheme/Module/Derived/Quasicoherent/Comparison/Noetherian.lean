module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Comparison.Qcqs

/-!
# Comparison for Noetherian schemes

The canonical comparison from the derived category of quasicoherent modules on a
Noetherian scheme is an equivalence, with the derived coherator as quasi-inverse.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- On a Noetherian scheme, the canonical comparison and the restricted derived coherator
are quasi-inverse. -/
theorem comparison_isQuasiInverse_of_isNoetherian {X : Scheme.{u}} [IsNoetherian X] :
    (comparison X).IsQuasiInverse
      ((DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι ⋙
        (Scheme.Modules.ringedSpaceEquivalence X).mapDerivedCategory.inverse ⋙
        QCoh.Derived.coherator X) := sorry

/-- On a Noetherian scheme, the canonical comparison from derived quasicoherent modules
to ambient derived modules with quasicoherent cohomology is an equivalence. -/
instance comparisonIsEquivalence (X : Scheme.{u}) [IsNoetherian X] :
    (comparison X).IsEquivalence := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
