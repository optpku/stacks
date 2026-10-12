/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.FppfRestriction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Parasitic.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Cohomology
public import ReasLib.CategoryTheory.Sites.Cohomology.Objectwise

/-!
# Cohomology under restriction from the big fppf site

This module compares objectwise cohomology on the big fppf site with
cohomology after restriction to the small Zariski or étale site.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.SmallStandardTopology.FppfRestriction

/-- For a big-fppf module sheaf whose selected small-site restriction is
quasi-coherent and whose canonical flat locally finitely presented base-change
maps are isomorphisms, objectwise fppf cohomology agrees with cohomology on the
selected small Zariski or small étale site. -/
theorem cohomology_isomorphic (σ : SmallStandardTopology) (S : Scheme.{u})
    (𝒢 : RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite .fppf S))
    [SheafOfModules.IsQuasicoherent ((restrict σ S).obj 𝒢)]
    (h_baseChange : IsBaseChangeCompatible σ 𝒢) (U : Over S) (p : ℕ)
    [Flat U.hom] [LocallyOfFinitePresentation U.hom]
    [HasSheafify (StandardTopology.fppf.overTopology S) AddCommGrpCat.{u}]
    [HasExt.{u}
      (Sheaf (StandardTopology.fppf.overTopology S) AddCommGrpCat.{u})]
    [HasSheafify (σ.topology U.left) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (σ.topology U.left) AddCommGrpCat.{u})] :
    IsIsomorphic
      ((Sheaf.cohomologyOverObjectFunctor
        (StandardTopology.fppf.overTopology S) U p).obj
          ((SheafOfModules.toSheaf
            (StandardTopology.Big.structureSheaf .fppf S)).obj 𝒢))
      ((Sheaf.functorH (σ.topology U.left) p).obj
        ((SheafOfModules.toSheaf
          (ringedSite σ U.left).structureSheaf).obj
            (restrictTo σ U.hom 𝒢))) := sorry

end AlgebraicGeometry.SmallStandardTopology.FppfRestriction
