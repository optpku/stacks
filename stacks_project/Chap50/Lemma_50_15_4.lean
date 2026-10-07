module

public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.LogPole.Wedge
import StacksCheckRecall

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.DeRham.LogPole

universe u

/- Lemma 50.15.4
The ordinary exterior products of relative forms extend uniquely to 𝒪_X-bilinear products of
logarithmic forms satisfying graded Leibniz. -/
@[stacks 0FUP]
#check (AlgebraicGeometry.RingedSpace.DeRham.LogPole.Canonical.existsUnique_wedgeFamily :
  ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X) [IsEffectiveCartierDivisor i]
    (h_defined : AlgebraicGeometry.RingedSpace.DeRham.LogPole.IsDefined f i),
    ∃! μ : AlgebraicGeometry.RingedSpace.DeRham.LogPole.Canonical.WedgeFamily f i,
      AlgebraicGeometry.RingedSpace.DeRham.LogPole.Canonical.IsWedgeFamily f i h_defined μ)

#check (AlgebraicGeometry.RingedSpace.DeRham.LogPole.Canonical.ordinaryHom :
  ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X) [IsEffectiveCartierDivisor i]
    (h_defined : AlgebraicGeometry.RingedSpace.DeRham.LogPole.IsDefined f i),
    SheafOfModules.RingedSite.DifferentialGradedAlgebra.Hom.{u, u, u}
      (AlgebraicGeometry.Scheme.DeRham.gaussManinDeRhamDGA f)
      (AlgebraicGeometry.RingedSpace.DeRham.LogPole.Canonical.dga f i h_defined))

#check (AlgebraicGeometry.RingedSpace.DeRham.LogPole.Canonical.exteriorPowerIso :
  ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X) [IsEffectiveCartierDivisor i]
    (h_defined : AlgebraicGeometry.RingedSpace.DeRham.LogPole.IsDefined f i) (p : ℕ),
    SheafOfModules.RingedSite.ExteriorPower.sheaf X.sheaf
      (AlgebraicGeometry.RingedSpace.DeRham.LogPole.Canonical.form f i 1) p ≅
      AlgebraicGeometry.RingedSpace.DeRham.LogPole.Canonical.form f i p)

#check (AlgebraicGeometry.RingedSpace.DeRham.LogPole.Canonical.residue_wedge :
  ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X) [IsEffectiveCartierDivisor i]
    (h_defined : AlgebraicGeometry.RingedSpace.DeRham.LogPole.IsDefined f i) (p q : ℕ),
    tensorHom
        (𝟙 (AlgebraicGeometry.RingedSpace.DeRham.LogPole.Canonical.term f i (p + 1) :
          AlgebraicGeometry.RingedSpace.DeRham.Modules f.toLRSHom.toShHom))
        (AlgebraicGeometry.RingedSpace.DeRham.LogPole.Canonical.ordinaryInclusionComponent f i q) ≫
      AlgebraicGeometry.RingedSpace.DeRham.LogPole.Canonical.wedgeComponent f i h_defined (p + 1) q ≫
      eqToHom
        (congrArg (fun n ↦
            (AlgebraicGeometry.RingedSpace.DeRham.LogPole.Canonical.term f i n :
              AlgebraicGeometry.RingedSpace.DeRham.Modules f.toLRSHom.toShHom))
          (AlgebraicGeometry.RingedSpace.DeRham.LogPole.Canonical.wedgeResidueDegree p q)) ≫
      AlgebraicGeometry.RingedSpace.DeRham.LogPole.Canonical.residueComponent f i h_defined (p + q) =
    tensorHom
        (AlgebraicGeometry.RingedSpace.DeRham.LogPole.Canonical.residueComponent f i h_defined p)
        (𝟙 (RingedSpace.DeRham.term f.toLRSHom.toShHom q)) ≫
      AlgebraicGeometry.RingedSpace.DeRham.LogPole.Canonical.divisorRightActionComponent f i p q)
