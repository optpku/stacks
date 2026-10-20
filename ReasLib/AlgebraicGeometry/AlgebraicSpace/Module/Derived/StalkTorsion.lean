module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealStalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.Complement
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.Algebra.Module.IdealPower.Serre

/-!
# Ideal-power torsion in derived étale stalks

Derived étale stalks of quasi-coherent complexes supported on a finitely presented
closed subspace have cohomology that is power torsion for its ideal-sheaf stalk.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- Every cohomology module of the derived étale stalk of a quasi-coherent complex
supported on a finitely presented closed subspace is power torsion for the stalk
of its defining ideal sheaf. -/
theorem stalkDerived_cohomology_isIdealPowerTorsion {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] [FinitePresentation i]
    (Q : DerivedQCoh X) (hQ : IsSupportedOn Q.obj (pointsImage i))
    (xbar : GeometricPoint X) (n : ℤ) :
    Module.IsIdealPowerTorsion (Hom.idealSheafStalkIdeal i xbar)
      ((DerivedCategory.homologyFunctor (ModuleCat (etaleLocalRing X xbar)) n).obj
        (stalkDerived xbar Q.obj)) :=
  sorry

/-- The derived étale stalk of a quasi-coherent complex supported on `|Z|` has
`Hom.idealSheafStalkIdeal i xbar`-power-torsion cohomology in every degree. -/
theorem stalkDerived_mem_idealPowerTorsion {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] [FinitePresentation i] (Q : DerivedQCoh X)
    (hQ : IsSupportedOn Q.obj (pointsImage i)) (xbar : GeometricPoint X) :
    DerivedCategory.cohomologyIn
      (ModuleCat.isIdealPowerTorsion (Hom.idealSheafStalkIdeal i xbar))
      (stalkDerived xbar Q.obj) :=
  fun n ↦ stalkDerived_cohomology_isIdealPowerTorsion i Q hQ xbar n

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
