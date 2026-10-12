/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.FppfRestriction.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Module.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Module.Quasicoherent.Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 35.12.4: for a big-fppf module sheaf whose selected small-site
restriction is quasi-coherent and whose canonical flat locally finitely
presented base-change maps are isomorphisms, objectwise fppf cohomology agrees
with cohomology on the selected small Zariski or small étale site. -/
@[stacks 0756] #check
  (AlgebraicGeometry.SmallStandardTopology.FppfRestriction.cohomology_isomorphic :
    ∀ (σ : SmallStandardTopology) (S : Scheme.{u})
      (𝒢 : RingedSite.ModuleCat.{u}
        (StandardTopology.Big.ringedSite .fppf S))
      [SheafOfModules.IsQuasicoherent
        ((SmallStandardTopology.FppfRestriction.restrict σ S).obj 𝒢)],
      SmallStandardTopology.FppfRestriction.IsBaseChangeCompatible σ 𝒢 →
      ∀ (U : Over S) (p : ℕ) [Flat U.hom] [LocallyOfFinitePresentation U.hom]
        [HasSheafify (StandardTopology.fppf.overTopology S) AddCommGrpCat.{u}]
        [HasExt.{u}
          (Sheaf (StandardTopology.fppf.overTopology S) AddCommGrpCat.{u})]
        [HasSheafify (σ.topology U.left) AddCommGrpCat.{u}]
        [HasExt.{u} (Sheaf (σ.topology U.left) AddCommGrpCat.{u})],
        IsIsomorphic
          ((Sheaf.cohomologyOverObjectFunctor
            (StandardTopology.fppf.overTopology S) U p).obj
              ((SheafOfModules.toSheaf
                (StandardTopology.Big.structureSheaf .fppf S)).obj 𝒢))
          ((Sheaf.functorH (σ.topology U.left) p).obj
            ((SheafOfModules.toSheaf
              (SmallStandardTopology.ringedSite σ U.left).structureSheaf).obj
                (SmallStandardTopology.FppfRestriction.restrictTo σ U.hom 𝒢))))
