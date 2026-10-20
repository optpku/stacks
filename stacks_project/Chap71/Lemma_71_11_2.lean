module

public import stacks_project.Chap71.Lemma_71_11_2_Restriction
public import stacks_project.Chap71.Lemma_71_11_2_RestrictionAdjunction
public import stacks_project.Chap71.Lemma_71_11_2_RestrictionBaseChange
public import stacks_project.Chap71.Lemma_71_11_2_RestrictionComposition
public import stacks_project.Chap71.Lemma_71_11_2_RestrictionMonoidal
public import stacks_project.Chap71.Lemma_71_11_2_RestrictionQuasiCoherent

public import stacks_project.Chap65.Lemma_65_11_3_OfRepresentable
public import stacks_project.Chap71.Lemma_71_11_2_Quadruple
public import stacks_project.Chap71.Lemma_71_11_2_Functor
public import stacks_project.Chap71.Lemma_71_11_2_Comparison

/-!
# Lemma 71.11.2

The functor of equivalence classes of relative projective quadruples is an algebraic
space, and its base change along a scheme morphism `g : Z ⟶ X` is the scheme-level
relative Proj of `g^* 𝒜`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.AlgebraicSpace.RelativeProj CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
/-- Lemma 71.11.2 (1): the functor `F` of equivalence classes of quadruples is an
algebraic space over `S`. -/
@[stacks 084B]
theorem isAlgebraicSpace (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg) :
    yoneda.relativelyRepresentable F.baseMap :=
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
  sorry

/-- Lemma 71.11.2 (2): for a morphism `g : Z ⟶ X` with `Z` a scheme, there is a
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

/-- The component of `baseChangeIso` at a test object is the component of the constructed
natural isomorphism. -/
theorem baseChangeIso_hom_app {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (T : (Over S)ᵒᵖ) :
    (baseChangeIso g F hF).hom.app T =
      (RelativeProjBaseChangeData.ofPushalong g F hF).toPullbackIso'.hom.app T :=
  sorry

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

/-- `pullbackOverSpaceMap` is the functor-level pullback map induced by `h`. -/
theorem pullbackOverSpaceMap_eq {Z Z' : Over S} (g : ofOver Z ⟶ X)
    (h : ofOver Z' ⟶ ofOver Z) (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg) :
    pullbackOverSpaceMap g h F hF =
      RelativeProjBaseChangeData.pullbackFunctorMap g h F :=
  sorry

/-- Lemma 71.11.2 (3): the canonical isomorphism is compatible with further base
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
