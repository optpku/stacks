module

public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.ModulePullback
public import ReasLib.CategoryTheory.Sites.Simplicial.LowerShriek

/-!
# Compatibility names for ringed simplex operators
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor ComplexShape
open RingedSite
open Sheaf.InternalModule (underlyingApp)

noncomputable section

universe u v w uA vA

namespace CategoryTheory.SimplicialSites

/-- Canonical derived-category structure on modules over a ringed site. -/
abbrev instHasDerivedCategory_moduleCat (X : RingedSite.{u, v, w})
    [UnivLE.{max u v, w}] :=
  Hom.moduleCat_hasDerivedCategory.{w, u, v, w} X

/-- The stage-inclusion natural transformation associated to a simplex operator. -/
abbrev ofStageNatTrans (C : SimplexCategory ⥤ Cat.{v, u})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (C.map φ).toFunctor ⋙ ofStage C n ⟶ ofStage C m :=
  stageInclusionWhisker C φ

end CategoryTheory.SimplicialSites
