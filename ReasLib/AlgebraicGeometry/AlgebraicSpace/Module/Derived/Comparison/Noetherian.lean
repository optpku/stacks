module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent
public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Basic

/-!
# Comparison for Noetherian algebraic spaces

The canonical comparison from the derived category of quasi-coherent modules on a
Noetherian algebraic space is an equivalence, with the restricted derived coherator
as quasi-inverse.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- On a Noetherian algebraic space, the canonical comparison
`DerivedCategory (QCoh X) ⥤ DerivedQCoh X` and the restricted derived coherator
`inclusion X ⋙ QCoh.Derived.coherator X` are quasi-inverse. -/
theorem comparison_isQuasiInverse_of_isNoetherian {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsNoetherian X] :
    (comparison X).IsQuasiInverse (inclusion X ⋙ QCoh.Derived.coherator X) :=
  sorry

/-- On a Noetherian algebraic space, the canonical comparison from derived quasi-coherent
modules to ambient derived modules with quasi-coherent cohomology is an equivalence. -/
instance comparisonIsEquivalence {S : Scheme.{u}} (X : AlgebraicSpace S) [IsNoetherian X] :
    (comparison X).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
