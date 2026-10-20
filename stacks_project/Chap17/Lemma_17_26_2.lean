module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Determinant.ExteriorPower
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Invertible
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.Determinant
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open SheafOfModules
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 17.26.2 (0FJN): on an arbitrary ringed space, the annihilator in `Λ(F)` of a flat
finitely presented module sheaf `F` is the determinant sheaf `det(F)`, and it is
tensor-invertible.  The exact ringed-space theorem and its reusable ringed-site owner are recalled
below. -/

@[stacks 0FJN]
#check @AlgebraicGeometry.RingedSpace.Determinant.subobject
#check @AlgebraicGeometry.RingedSpace.Determinant.factors_iff
#check fun {X : RingedSpace.{u}} (F : X.Modules)
    [F.IsFinitePresentation] [F.IsFlat] ↦
  (inferInstance : isInvertibleObject (RingedSpace.Determinant.sheaf F))
#check @SheafOfModules.RingedSite.Determinant.isInvertible
#check @SheafOfModules.RingedSite.Determinant.isInvertible_of_isLocal

/- On a locally ringed space the 0FJN conclusion upgrades to finite local freeness of rank one,
without adding a stalk-local hypothesis to the original arbitrary-ringed-space statement. -/

#check @AlgebraicGeometry.LocallyRingedSpace.Determinant.rankOne
#check @AlgebraicGeometry.RingedSpace.rankOne_of_isInvertible

/- For a fixed-rank finite locally free module, the determinant comparison is explicit: its
forward map projects the determinant inclusion to top degree, and its inverse is the homogeneous
inclusion lifted through the determinant kernel. -/

#check fun {X : RingedSpace.{u}} (F : X.Modules) (r : ℕ) ↦
  (RingedSite.Determinant.topHom X.sheaf F r :
    RingedSpace.Determinant.sheaf F ⟶ RingedSpace.ExteriorPower.sheaf F r)
#check fun {X : RingedSpace.{u}} (F : X.Modules) (r : ℕ)
    [IsFiniteLocallyFreeOfRank r F] ↦
  (RingedSite.Determinant.topInv X.sheaf F r :
    RingedSpace.ExteriorPower.sheaf F r ⟶ RingedSpace.Determinant.sheaf F)
#check fun {X : RingedSpace.{u}} (F : X.Modules) (r : ℕ)
    [IsFiniteLocallyFreeOfRank r F] ↦
  (RingedSite.Determinant.topIso X.sheaf F r :
    RingedSpace.Determinant.sheaf F ≅ RingedSpace.ExteriorPower.sheaf F r)
#check fun {X : RingedSpace.{u}} (F : X.Modules) (r : ℕ)
    [IsFiniteLocallyFreeOfRank r F] ↦
  RingedSite.Determinant.topInv_ι X.sheaf F r
#check fun {X : RingedSpace.{u}} (F : X.Modules) (r : ℕ)
    [IsFiniteLocallyFreeOfRank r F] ↦
  RingedSite.Determinant.topIso_hom_powerι X.sheaf F r
#check fun {X : RingedSpace.{u}} {F G : X.Modules} (e : F ≅ G) ↦
  RingedSite.Determinant.mapIso e
#check fun {X : RingedSpace.{u}} {F G : X.Modules} (e : F ≅ G) ↦
  RingedSite.Determinant.mapIso_hom_ι e
#check fun {X : RingedSpace.{u}} {F G : X.Modules} (e : F ≅ G) (r : ℕ)
    [IsFiniteLocallyFreeOfRank r F] [IsFiniteLocallyFreeOfRank r G] ↦
  RingedSite.Determinant.mapIso_hom_topIso X.sheaf e r
#check @SheafOfModules.RingedSite.ExteriorPower.top_rankOne
#check @SheafOfModules.RingedSite.ExteriorPower.top_isInvertible
