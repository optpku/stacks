/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.BaseChange
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Instances
public import ReasLib.Topology.Sheaves.CommRing.Pushforward
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open SheafOfModules.RingedSite

universe u

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}

/- Lemma 71.11.2. The relative projective functor is an algebraic space, with
canonical scheme base change compatible with further base change. -/
@[stacks 084B] #check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.baseMap_relativelyRepresentable :
    ∀ (F : ProjFunctor X 𝒜)
    (deg : DegreePieces 𝒜) (hF : F.IsAssociatedToQuadruples deg),
    yoneda.relativelyRepresentable F.baseMap)

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.baseChangeIso :
    ∀ {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)],
    ofOver (relativeProjOver g deg) ≅ pullbackOverSpace g F hF)

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.baseChangeIso_comp :
    ∀ {Z Z' : Over S} (g : ofOver Z ⟶ X)
    (h : ofOver Z' ⟶ ofOver Z)
    (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    [F_Z' : AlgebraicGeometry.RelativeProjFunctor Z'.left
      (pullbackAlgebra (h ≫ g) deg)],
    (baseChangeIso (h ≫ g) F hF).hom ≫
        pullbackOverSpaceMap g h F hF =
      ofOverMap (RelativeProjBaseChangeData.furtherRelativeProjMap g h F hF) ≫
        (baseChangeIso g F hF).hom)
