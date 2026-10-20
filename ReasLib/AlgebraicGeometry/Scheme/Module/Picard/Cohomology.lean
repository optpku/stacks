/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Picard
public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf.LocallyRinged
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Picard.Cohomology.Equiv
public import ReasLib.AlgebraicGeometry.RingedSpace.LocallyRinged

/-!
# Picard groups and units cohomology of schemes
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (τ : StandardTopology) (X : Scheme.{u})

/-- The canonical homomorphism from the scheme Picard group to first cohomology of the units on a
standard big site. -/
noncomputable def bigPicardCohomologyHom
    [HasExt.{u + 1} (Sheaf (τ.overTopology X) AddCommGrpCat.{u + 1})] :
    X.PicardGroup →+ (CategoryTheory.Sheaf.unitsAddSheaf
      (AssociatedModule.bigCommStructureSheaf τ X)).H 1 :=
  (SheafOfModules.RingedSite.PicardGroup.cohomologyClass
      (AssociatedModule.bigCommStructureSheaf τ X)).comp
    (AssociatedModule.picardMap τ X)

/-- The inverse function attached to the specified Picard-to-cohomology homomorphism. -/
noncomputable def bigPicardCohomologyInverse
    [HasExt.{u + 1} (Sheaf (τ.overTopology X) AddCommGrpCat.{u + 1})] :
    (CategoryTheory.Sheaf.unitsAddSheaf
      (AssociatedModule.bigCommStructureSheaf τ X)).H 1 → X.PicardGroup :=
  Function.invFun (bigPicardCohomologyHom τ X)

/-- The inverse function is a left inverse of the canonical Picard-to-cohomology homomorphism. -/
theorem bigPicardCohomologyInverse_hom
    [HasExt.{u + 1} (Sheaf (τ.overTopology X) AddCommGrpCat.{u + 1})] :
    Function.LeftInverse (bigPicardCohomologyInverse τ X)
      (bigPicardCohomologyHom τ X) := sorry

/-- The canonical Picard-to-cohomology homomorphism is a right inverse of its inverse function. -/
theorem bigPicardCohomologyHom_inverse
    [HasExt.{u + 1} (Sheaf (τ.overTopology X) AddCommGrpCat.{u + 1})] :
    Function.RightInverse (bigPicardCohomologyInverse τ X)
      (bigPicardCohomologyHom τ X) := sorry

/-- The canonical Picard-to-cohomology homomorphism sends a scheme Picard representative to the
cohomology class of its associated-module generator torsor. -/
theorem bigPicardCohomologyHom_mk
    [HasExt.{u + 1} (Sheaf (τ.overTopology X) AddCommGrpCat.{u + 1})]
    (L : X.Modules) [isInvertibleObject L] :
    bigPicardCohomologyHom τ X (Modules.picardClass L) =
      SheafOfModules.RingedSite.PicardGroup.cohomologyClass
        (AssociatedModule.bigCommStructureSheaf τ X)
        (MonoidalCategory.PicardGroup.mk (AssociatedModule.bigComm τ X L)) := sorry

/-- The additive equivalence between the scheme Picard group and big-site units cohomology. -/
noncomputable def picardEquivBigUnitsH1
    [HasExt.{u + 1} (Sheaf (τ.overTopology X) AddCommGrpCat.{u + 1})] :
    X.PicardGroup ≃+
      (CategoryTheory.Sheaf.unitsAddSheaf
        (AssociatedModule.bigCommStructureSheaf τ X)).H 1 where
  toFun := bigPicardCohomologyHom τ X
  invFun := bigPicardCohomologyInverse τ X
  left_inv := bigPicardCohomologyInverse_hom τ X
  right_inv := bigPicardCohomologyHom_inverse τ X
  map_add' := (bigPicardCohomologyHom τ X).map_add

/-- The canonical additive equivalence from big-site units cohomology to the scheme Picard group. -/
noncomputable def h1BigEquivPicard
    [HasExt.{u + 1} (Sheaf (τ.overTopology X) AddCommGrpCat.{u + 1})] :
    (CategoryTheory.Sheaf.unitsAddSheaf
      (AssociatedModule.bigCommStructureSheaf τ X)).H 1 ≃+ X.PicardGroup :=
  (picardEquivBigUnitsH1 τ X).symm

/-- Big-site cohomology groups for two standard topologies are canonically identified through the
same scheme Picard group. -/
noncomputable def h1BigEquivH1Big
    (σ : StandardTopology)
    [HasExt.{u + 1} (Sheaf (τ.overTopology X) AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf (σ.overTopology X) AddCommGrpCat.{u + 1})] :
    (CategoryTheory.Sheaf.unitsAddSheaf
      (AssociatedModule.bigCommStructureSheaf τ X)).H 1 ≃+
      (CategoryTheory.Sheaf.unitsAddSheaf
        (AssociatedModule.bigCommStructureSheaf σ X)).H 1 :=
  (h1BigEquivPicard τ X).trans (h1BigEquivPicard σ X).symm

/-- The canonical comparison from big fppf cohomology to big syntomic cohomology. -/
noncomputable def h1FppfEquivH1Syntomic
    [HasSheafify (StandardTopology.fppf.overTopology X) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (StandardTopology.fppf.overTopology X) AddCommGrpCat.{u + 1})]
    [HasSheafify (StandardTopology.syntomic.overTopology X) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (StandardTopology.syntomic.overTopology X)
      AddCommGrpCat.{u + 1})] :
    (CategoryTheory.Sheaf.unitsAddSheaf
      (AssociatedModule.bigCommStructureSheaf .fppf X)).H 1 ≃+
      (CategoryTheory.Sheaf.unitsAddSheaf
        (AssociatedModule.bigCommStructureSheaf .syntomic X)).H 1 :=
  h1BigEquivH1Big StandardTopology.fppf X StandardTopology.syntomic

/-- The canonical comparison from big syntomic cohomology to big smooth cohomology. -/
noncomputable def h1SyntomicEquivH1Smooth
    [HasSheafify (StandardTopology.syntomic.overTopology X) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (StandardTopology.syntomic.overTopology X) AddCommGrpCat.{u + 1})]
    [HasSheafify (StandardTopology.smooth.overTopology X) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (StandardTopology.smooth.overTopology X)
      AddCommGrpCat.{u + 1})] :
    (CategoryTheory.Sheaf.unitsAddSheaf
      (AssociatedModule.bigCommStructureSheaf .syntomic X)).H 1 ≃+
      (CategoryTheory.Sheaf.unitsAddSheaf
        (AssociatedModule.bigCommStructureSheaf .smooth X)).H 1 :=
  h1BigEquivH1Big StandardTopology.syntomic X StandardTopology.smooth

/-- The canonical comparison from big smooth cohomology to big étale cohomology. -/
noncomputable def h1SmoothEquivH1Etale
    [HasSheafify (StandardTopology.smooth.overTopology X) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (StandardTopology.smooth.overTopology X) AddCommGrpCat.{u + 1})]
    [HasSheafify (StandardTopology.etale.overTopology X) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (StandardTopology.etale.overTopology X)
      AddCommGrpCat.{u + 1})] :
    (CategoryTheory.Sheaf.unitsAddSheaf
      (AssociatedModule.bigCommStructureSheaf .smooth X)).H 1 ≃+
      (CategoryTheory.Sheaf.unitsAddSheaf
        (AssociatedModule.bigCommStructureSheaf .etale X)).H 1 :=
  h1BigEquivH1Big StandardTopology.smooth X StandardTopology.etale

/-- The canonical comparison from big étale cohomology to big Zariski cohomology. -/
noncomputable def h1EtaleEquivH1Zariski
    [HasSheafify (StandardTopology.etale.overTopology X) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (StandardTopology.etale.overTopology X) AddCommGrpCat.{u + 1})]
    [HasSheafify (StandardTopology.zariski.overTopology X) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (StandardTopology.zariski.overTopology X)
      AddCommGrpCat.{u + 1})] :
    (CategoryTheory.Sheaf.unitsAddSheaf
      (AssociatedModule.bigCommStructureSheaf .etale X)).H 1 ≃+
      (CategoryTheory.Sheaf.unitsAddSheaf
        (AssociatedModule.bigCommStructureSheaf .zariski X)).H 1 :=
  h1BigEquivH1Big StandardTopology.etale X StandardTopology.zariski

/-- The canonical comparison from big Zariski cohomology to the scheme Picard group. -/
noncomputable def h1ZariskiEquivPicard
    [HasSheafify (StandardTopology.zariski.overTopology X) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (StandardTopology.zariski.overTopology X)
      AddCommGrpCat.{u + 1})] :
    (CategoryTheory.Sheaf.unitsAddSheaf
      (AssociatedModule.bigCommStructureSheaf .zariski X)).H 1 ≃+ X.PicardGroup :=
  h1BigEquivPicard .zariski X

/-- The canonical comparison between the scheme Picard group and cohomology of units on the
opens site. -/
noncomputable def picardEquivUnitsH1 (X : Scheme.{u})
    [HasSheafify (Opens.grothendieckTopology X.toRingedSpace) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.toRingedSpace) AddCommGrpCat.{u})] :
    X.PicardGroup ≃+
      (CategoryTheory.Sheaf.unitsAddSheaf X.toRingedSpace.sheaf).H 1 :=
  SheafOfModules.RingedSite.PicardGroup.cohomologyEquiv X.toRingedSpace.sheaf

variable {X : Scheme.{u}}
variable [HasSheafify (Opens.grothendieckTopology X.toRingedSpace) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.toRingedSpace) AddCommGrpCat.{u})]

/-- First cohomology of the structure-sheaf units is a nonzero object when the scheme's
Picard group is nontrivial. -/
theorem unitsAddSheaf_functorH_one_not_isZero [Nontrivial X.PicardGroup] :
    ¬ CategoryTheory.Limits.IsZero
        ((Sheaf.functorH (Opens.grothendieckTopology X.toRingedSpace) 1).obj
          (Sheaf.unitsAddSheaf X.toRingedSpace.sheaf)) :=
  sorry

/-- The degree-one cohomology functor on abelian sheaves is nonzero for every scheme with
nontrivial Picard group. -/
theorem functorH_one_not_isZero [Nontrivial X.PicardGroup] :
    ¬ CategoryTheory.Limits.IsZero
      (Sheaf.functorH (Opens.grothendieckTopology X.toRingedSpace) 1) :=
  sorry

end AlgebraicGeometry.Scheme
