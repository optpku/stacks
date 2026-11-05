/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.BaseChange.SchemeGluing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.BaseChange.QuadruplePushalong
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.BaseChange.PointEquiv

/-!
# Base change for relative projective functors of algebraic spaces

Relative representability and the canonical Stacks 084B base-change isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Sheaf.InternalModule
open SheafOfModules SheafOfModules.RingedSite
open AlgebraicGeometry.AlgebraicSpace.ReasLibPullback
open scoped ZeroObject

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}

/-- The structural map of a relative projective functor associated to quadruples is
representable. -/
theorem baseMap_relativelyRepresentable {𝒜} (F : ProjFunctor X 𝒜)
    (deg : DegreePieces 𝒜) (hF : F.IsAssociatedToQuadruples deg) :
    yoneda.relativelyRepresentable F.baseMap :=
  sorry

/-- The algebraic space over `S` whose functor of points is a relative projective functor
associated to quadruples. -/
def toAlgebraicSpace {𝒜} (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg) : AlgebraicSpace S :=
  ofRelativelyRepresentable F.baseMap (baseMap_relativelyRepresentable F deg hF)

/-- The functor of points of `toAlgebraicSpace F hF` is the underlying functor of `F`. -/
theorem toAlgebraicSpace_functorOfPoints {𝒜} (F : ProjFunctor X 𝒜)
    {deg : DegreePieces 𝒜} (hF : F.IsAssociatedToQuadruples deg) :
    (toAlgebraicSpace F hF).functorOfPoints = F.toFunctor :=
  sorry

/-- The structure morphism `π : toAlgebraicSpace F ⟶ X` is the stored base map of `F`. -/
def toAlgebraicSpace_hom {𝒜} (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg) :
    toAlgebraicSpace F hF ⟶ X :=
  ofRelativelyRepresentable_hom F.baseMap (baseMap_relativelyRepresentable F deg hF)

/-- `toAlgebraicSpace_hom F hF` is the stored base map of `F`. -/
theorem toAlgebraicSpace_hom_eq {𝒜} (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg) :
    toAlgebraicSpace_hom F hF = F.baseMap :=
  sorry


/-- The fibre product `Z ×_X F` as an algebraic space. -/
def pullbackOverSpace {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    {deg : DegreePieces 𝒜} (hF : F.IsAssociatedToQuadruples deg) :
    AlgebraicSpace S :=
  pullbackOver g (toAlgebraicSpace_hom F hF) X.isSheaf X.representableDiagonal

/-- The functor of points of `pullbackOverSpace g F hF` is the categorical pullback of
`g` and `F.baseMap`. -/
theorem pullbackOverSpace_functorOfPoints {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg) :
    (pullbackOverSpace g F hF).functorOfPoints = functorPullback g F :=
  rfl

/-- For a morphism `g : Z ⟶ X` with `Z` a scheme, there is a
canonical isomorphism `underline{Proj}_Z(g^* 𝒜) = Z ×_X F`. -/
@[stacks 084B]
def baseChangeIso {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)] :
    ofOver (relativeProjOver g deg) ≅ pullbackOverSpace g F hF where
  hom := (RelativeProjBaseChangeData.ofPushalong g F hF).toPullbackIso'.hom
  inv := (RelativeProjBaseChangeData.ofPushalong g F hF).toPullbackIso'.inv
  hom_inv_id :=
    (RelativeProjBaseChangeData.ofPushalong g F hF).toPullbackIso'.hom_inv_id
  inv_hom_id :=
    (RelativeProjBaseChangeData.ofPushalong g F hF).toPullbackIso'.inv_hom_id

/-- The isomorphism `underline{Proj}_Z(g^* 𝒜) ≅ Z ×_X F` commutes with the structure
maps to `Z`. -/
theorem baseChangeIso_fst {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)] :
    (baseChangeIso g F hF).hom ≫
        pullbackOverFst g (toAlgebraicSpace_hom F hF) X.isSheaf
          X.representableDiagonal =
      yoneda.map (relativeProjToZ g deg) :=
  sorry

/-- The morphism `Z' ×_X F ⟶ Z ×_X F` induced by a morphism of schemes `h : Z' ⟶ Z`
over `X`. -/
def pullbackOverSpaceMap {Z Z' : Over S} (g : ofOver Z ⟶ X)
    (h : ofOver Z' ⟶ ofOver Z) (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg) :
    pullbackOverSpace (h ≫ g) F hF ⟶ pullbackOverSpace g F hF :=
  RelativeProjBaseChangeData.pullbackFunctorMap g h F

/-- The canonical isomorphism is compatible with further base
change along a morphism of schemes over `S`. -/
@[stacks 084B]
theorem baseChangeIso_comp {Z Z' : Over S} (g : ofOver Z ⟶ X)
    (h : ofOver Z' ⟶ ofOver Z)
    (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    [F_Z' : AlgebraicGeometry.RelativeProjFunctor Z'.left
      (pullbackAlgebra (h ≫ g) deg)] :
    (baseChangeIso (h ≫ g) F hF).hom ≫
        pullbackOverSpaceMap g h F hF =
      ofOverMap (RelativeProjBaseChangeData.furtherRelativeProjMap g h F hF) ≫
        (baseChangeIso g F hF).hom :=
  sorry


end AlgebraicGeometry.AlgebraicSpace.RelativeProj
