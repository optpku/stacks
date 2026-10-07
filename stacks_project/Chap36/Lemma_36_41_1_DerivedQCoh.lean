module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.SiteModels
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»

open CategoryTheory

universe u

/- Compatibility bridge for the affine-site presentations of derived quasi-coherent modules. -/
#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.affineCommStructurePresheaf :
    ∀ (X : AlgebraicGeometry.Scheme.{u}),
      (AlgebraicGeometry.SmallStandardTopology.Affine.site .zariski X)ᵒᵖ ⥤
        CommRingCat.{u + 1})
