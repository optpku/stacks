module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.IdealPower.Graded

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 30.20.2
For a proper morphism to a locally Noetherian scheme, the graded higher direct images
of ideal-power products are quasi-coherent and of finite type over the Rees algebra.
-/
@[stacks 02O9] #check
  (AlgebraicGeometry.Scheme.Hom.IdealPowerCohomology.isFiniteType :
    ∀ {Y : Scheme.{u}} (I : Y.IdealSheafData) [I.toModule.IsQuasicoherent]
      {X : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (p : ℕ)
      [IsLocallyNoetherian Y] [IsProper f] [F.IsCoherent],
      SheafOfModules.RingedSite.GradedModuleSheaf.IsLocallyFiniteType.{u, u}
        (AlgebraicGeometry.Scheme.Hom.IdealPowerCohomology.gradedModule I f F p))

#check
  (AlgebraicGeometry.Scheme.Hom.IdealPowerCohomology.isQuasicoherent :
    ∀ {Y : Scheme.{u}} (I : Y.IdealSheafData) [I.toModule.IsQuasicoherent]
      {X : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (p : ℕ)
      [IsLocallyNoetherian Y] [IsProper f] [F.IsCoherent] (n : ℤ),
      ((AlgebraicGeometry.Scheme.Hom.IdealPowerCohomology.gradedModule I f F p).obj n).IsQuasicoherent)
