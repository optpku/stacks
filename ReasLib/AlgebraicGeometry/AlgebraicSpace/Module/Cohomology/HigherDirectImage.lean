module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PresentationRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.IntegerDegree
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage.IntegerDegree

/-!
# Cohomology of higher direct images on affine étale objects

For a quasi-compact quasi-separated morphism, cohomology on an affine étale pullback
is isomorphic to degree-zero cohomology of the corresponding higher direct image.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Étale cohomology of an `𝒪_X`-module on the fibre product of an object of `Y_étale` with `X`. -/
abbrev cohomologyOnEtalePullback (f : X ⟶ Y) (F : X.Modules) (V : smallEtaleSite Y) (q : ℤ)
    [HasSheafify (smallEtaleTopology (Limits.pullback V.hom f)) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology (Limits.pullback V.hom f)) AddCommGrpCat.{u})] :
    AddCommGrpCat.{u} :=
  AlgebraicSpace.cohomologyInt (Limits.pullback V.hom f) (restrict F (Limits.pullback.snd V.hom f)) q

/-- Degree-zero objectwise cohomology of a higher direct image at an object of `Y_étale`. -/
abbrev higherDirectImage_degreeZero_cohomology (f : X ⟶ Y) (F : X.Modules)
    (V : smallEtaleSite Y) (q : ℤ)
    [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u})] :
    AddCommGrpCat.{u} :=
  Sheaf.H' ((SheafOfModules.toSheaf (structureSheaf Y)).obj (higherDirectImageInt f F q)) 0 V

/-- For a quasi-compact quasi-separated morphism and a quasi-coherent module, cohomology
on the pullback of an affine étale object is isomorphic to degree-zero objectwise cohomology
of the corresponding higher direct image in every integer degree. -/
theorem cohomology_iso_higherDirectImage_degreeZero (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]
    (F : X.Modules) [F.IsQuasicoherent]
    (V : smallEtaleSite Y) [AlgebraicGeometry.IsAffine V.left.left] (q : ℤ)
    [HasSheafify (smallEtaleTopology (Limits.pullback V.hom f)) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology (Limits.pullback V.hom f)) AddCommGrpCat.{u})]
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u})] :
    IsIsomorphic (cohomologyOnEtalePullback f F V q)
      (higherDirectImage_degreeZero_cohomology f F V q) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
