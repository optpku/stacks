module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import stacks_project.Chap66.Proposition_66_32_1_Comparison
public import stacks_project.Chap78.Lemma_78_12_3_QCoh
public import stacks_project.Chap94.Definition_94_16_5_Presentation
public import stacks_project.Chap94.Lemma_94_16_2_Presentation
public import stacks_project.Chap94.«94_8_2_1_FullyFaithful»
public import stacks_project.Chap103.Definition_103_7_1_FlatBaseChange
public import stacks_project.Chap104.Definition_104_5_1_LQCohFbc

/-!
# Descent of locally quasi-coherent modules with flat base change

The inclusion `QCoh(𝒪_X) ⥤ LQCoh^{fbc}(𝒪_X)` and the descent functor `q₂` sending an
object `F` of `LQCoh^{fbc}` to the equivariant module `(f^* F|_{U_étale}, α)` on a
smooth presentation of an algebraic stack.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry.GroupoidsOver
open AlgebraicGeometry.GroupoidAlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicStack
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The scheme atlas extracted from the algebraic-stack axiom. -/
def algebraicStackAtlasOver (X : GroupoidsOver S) [AlgebraicStack X] : Over S :=
  (inferInstance : AlgebraicStack X).existsSmoothSurjectiveAtlas.choose

/-- The smooth surjective `1`-morphism from the chosen scheme atlas. -/
def algebraicStackAtlasHom (X : GroupoidsOver S) [AlgebraicStack X] :
    GroupoidsOver.slice (algebraicStackAtlasOver X) ⟶ X :=
  (inferInstance : AlgebraicStack X).existsSmoothSurjectiveAtlas.choose_spec.choose

/-- The chosen atlas `1`-morphism is smooth. -/
instance algebraicStackAtlasHom.smooth (X : GroupoidsOver S) [AlgebraicStack X] :
    AlgebraicGeometry.Groupoids.Hom.Smooth (algebraicStackAtlasHom X) :=
  (inferInstance : AlgebraicStack X).existsSmoothSurjectiveAtlas.choose_spec.choose_spec.1

/-- The chosen atlas `1`-morphism is surjective. -/
instance algebraicStackAtlasHom.surjective (X : GroupoidsOver S) [AlgebraicStack X] :
    AlgebraicGeometry.Groupoids.Hom.Surjective (algebraicStackAtlasHom X) :=
  (inferInstance : AlgebraicStack X).existsSmoothSurjectiveAtlas.choose_spec.choose_spec.2

/-- A canonical slice is representable by the algebraic space `ofOver U`. -/
theorem sliceRepresentable (U : Over S) :
    IsRepresentableByAlgebraicSpace (GroupoidsOver.slice U) :=
  ⟨ofOver U, ⟨(ofOverSliceEquiv U).symm⟩⟩

/-- A chosen smooth presentation of an algebraic stack, obtained from a scheme atlas. -/
def algebraicStackPresentation (X : GroupoidsOver S) [AlgebraicStack X] :
    Presentation X :=
  Presentation.ofSmoothSurjective (algebraicStackAtlasHom X)
    (sliceRepresentable (algebraicStackAtlasOver X))

/-- The object of `X` obtained by evaluating a slice `1`-morphism at the identity. -/
def objectOfHom {X : GroupoidsOver S} {U : Over S}
    (f : GroupoidsOver.slice U ⟶ X) : X.total :=
  (FiberedCategoryOver.Groupoids.toFunctor f).obj (Over.mk (𝟙 U))

/-- The object of `X` obtained by evaluating the chosen atlas at the identity of `U`. -/
def algebraicStackAtlasObject (X : GroupoidsOver S) [AlgebraicStack X] : X.total :=
  objectOfHom (algebraicStackAtlasHom X)

/-- The inclusion of quasi-coherent modules into locally quasi-coherent étale modules
with the flat base change property. -/
def QCoh.toLQCohFbc (X : GroupoidsOver S) [AlgebraicStack X] :
    QCoh X ⥤ LQCohFbc X :=
  (lqcohFbc X).lift (QCoh.inclusion X ⋙ restriction X) (fun _ ↦ sorry)

/-- The underlying étale module of `toLQCohFbc` is restriction of the fppf quasi-coherent sheaf. -/
theorem QCoh.toLQCohFbc_comp_inclusion (X : GroupoidsOver S) [AlgebraicStack X] :
    QCoh.toLQCohFbc X ⋙ LQCohFbc.inclusion X =
      QCoh.inclusion X ⋙ restriction X :=
  rfl

/-- The inclusion of quasi-coherent modules into locally quasi-coherent étale
modules with the flat base change property is full. -/
instance QCoh.toLQCohFbc_full (X : GroupoidsOver S) [AlgebraicStack X] :
    (QCoh.toLQCohFbc X).Full :=
  sorry

/-- The inclusion of quasi-coherent modules into locally quasi-coherent étale
modules with the flat base change property is faithful. -/
instance QCoh.toLQCohFbc_faithful (X : GroupoidsOver S) [AlgebraicStack X] :
    (QCoh.toLQCohFbc X).Faithful :=
  sorry

/-- The test scheme underlying the atlas object of `X`. -/
def algebraicStackAtlasTest (X : GroupoidsOver S) [AlgebraicStack X] : Over S :=
  X.p.obj (algebraicStackAtlasObject X)

/-- Restriction of an étale `LQCoh^{fbc}` module to the small étale site of the atlas object. -/
def LQCohFbc.atlasSchemeModule (X : GroupoidsOver S) [AlgebraicStack X]
    (F : LQCohFbc X) :
    RingedSite.ModuleCat.{u}
      (Scheme.Etale.Small.ringedSite (algebraicStackAtlasTest X).left) :=
  (restrictModulesToSmallEtale X (algebraicStackAtlasObject X)).obj
    ((LQCohFbc.inclusion X).obj F)

/-- A morphism of `LQCoh^{fbc}` modules induces a morphism of atlas small-étale restrictions. -/
def LQCohFbc.atlasSchemeModuleMap (X : GroupoidsOver S) [AlgebraicStack X]
    {F F' : LQCohFbc X} (f : F ⟶ F') :
    LQCohFbc.atlasSchemeModule X F ⟶ LQCohFbc.atlasSchemeModule X F' :=
  (restrictModulesToSmallEtale X (algebraicStackAtlasObject X)).map
    ((LQCohFbc.inclusion X).map f)

/-- Pushforward of modules along `schemeEtaleRingedHom` of the atlas test scheme is a
right adjoint. -/
instance algebraicStackAtlasTest.modulePushforward_isRightAdjoint
    (X : GroupoidsOver S) [AlgebraicStack X] :
    ((schemeEtaleRingedHom (algebraicStackAtlasTest X)).modulePushforward.{u}).IsRightAdjoint :=
  sorry

/-- Inverse image transporting small-étale modules on the atlas scheme to modules on
`ofOver` of the atlas test scheme. -/
def LQCohFbc.atlasSpaceModulesLeft (X : GroupoidsOver S) [AlgebraicStack X] :
    RingedSite.ModuleCat.{u}
        (Scheme.Etale.Small.ringedSite (algebraicStackAtlasTest X).left) ⥤
      AlgebraicSpace.Modules (ofOver (algebraicStackAtlasTest X)) :=
  (schemeEtaleRingedHom (algebraicStackAtlasTest X)).modulePullback.{u}

/-- Transport of the atlas small-étale restriction to `𝒪_{ofOver U}`-modules. -/
def LQCohFbc.atlasSpaceModule (X : GroupoidsOver S) [AlgebraicStack X]
    (F : LQCohFbc X) :
    AlgebraicSpace.Modules (ofOver (algebraicStackAtlasTest X)) :=
  (LQCohFbc.atlasSpaceModulesLeft X).obj (LQCohFbc.atlasSchemeModule X F)

/-- Quasi-coherent lift of `atlasSpaceModule`. -/
def LQCohFbc.atlasSpaceQCoh (X : GroupoidsOver S) [AlgebraicStack X]
    (F : LQCohFbc X) :
    AlgebraicSpace.QCoh (ofOver (algebraicStackAtlasTest X)) :=
  ⟨LQCohFbc.atlasSpaceModule X F, sorry⟩

/-- Equivalence identifying the chosen slice with `ofOver U`. -/
def algebraicStackAtlasSliceEquiv (X : GroupoidsOver S) [AlgebraicStack X] :
    GroupoidsOver.slice (algebraicStackAtlasOver X) ≌
      (ofOver (algebraicStackAtlasOver X)).toGroupoids :=
  (ofOverSliceEquiv (algebraicStackAtlasOver X)).symm

/-- Equivalence identifying the chosen slice with its representing algebraic space. -/
def algebraicStackAtlasRepresentingEquiv (X : GroupoidsOver S) [AlgebraicStack X] :
    GroupoidsOver.slice (algebraicStackAtlasOver X) ≌
      (representingSpace (sliceRepresentable (algebraicStackAtlasOver X))).toGroupoids :=
  representingEquiv (sliceRepresentable (algebraicStackAtlasOver X))

/-- The comparison morphism from the presentation object space to `ofOver U`. -/
def algebraicStackObjectSpaceHom (X : GroupoidsOver S) [AlgebraicStack X] :
    (algebraicStackPresentation X).groupoid.U.left ⟶
      ofOver (algebraicStackAtlasOver X) :=
  extendBaseIdHom (representingSpace (sliceRepresentable (algebraicStackAtlasOver X))) ≫
    AlgebraicSpace.toGroupoids.recover
      (algebraicStackAtlasRepresentingEquiv X) (algebraicStackAtlasSliceEquiv X) (𝟙 _)

/-- Identification of the atlas test scheme with the chosen atlas `Over S`. -/
theorem algebraicStackAtlasTest_eq (X : GroupoidsOver S) [AlgebraicStack X] :
    algebraicStackAtlasTest X = algebraicStackAtlasOver X :=
  sorry

/-- The morphism `ofOver atlasOver ⟶ ofOver atlasTest` induced by base-commutativity of
the atlas `1`-morphism. -/
def algebraicStackAtlasOverToTest (X : GroupoidsOver S) [AlgebraicStack X] :
    ofOver (algebraicStackAtlasOver X) ⟶ ofOver (algebraicStackAtlasTest X) :=
  ofOverMap
    (eqToHom
      (congrArg (fun F ↦ F.obj (Over.mk (𝟙 (algebraicStackAtlasOver X))))
        (comm (algebraicStackAtlasHom X))).symm)

/-- Restriction of `atlasSpaceQCoh` to the presentation object space, after identifying
the atlas test scheme with the chosen atlas. -/
def LQCohFbc.atlasRestrict (X : GroupoidsOver S) [AlgebraicStack X]
    (F : LQCohFbc X) :
    AlgebraicSpace.QCoh (algebraicStackPresentation X).groupoid.U.left :=
  (AlgebraicSpace.QCoh.pullback (algebraicStackObjectSpaceHom X)).obj
    ((AlgebraicSpace.QCoh.pullback (algebraicStackAtlasOverToTest X)).obj
      (LQCohFbc.atlasSpaceQCoh X F))

/-- Source and target of the presenting groupoid induce the same structure morphism to
`ofOver` of the atlas after composing with the object-space comparison. This records
that both projections of `U ×_X U` lie over the atlas. -/
theorem algebraicStackPresentation_source_target_comp (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (algebraicStackPresentation X).groupoid.t.left ≫
        algebraicStackObjectSpaceHom X ≫ algebraicStackAtlasOverToTest X =
      (algebraicStackPresentation X).groupoid.s.left ≫
        algebraicStackObjectSpaceHom X ≫ algebraicStackAtlasOverToTest X :=
  sorry

/-- The equivariance map `α : t^* (f^* F|_{U_étale}) ⟶ s^* (f^* F|_{U_étale})` of `q₂(F)`,
as the transport of the identity on the atlas restriction along the two projections. -/
def LQCohFbc.atlasAction (X : GroupoidsOver S) [AlgebraicStack X]
    (F : LQCohFbc X) :
    (AlgebraicSpace.QCoh.pullback (algebraicStackPresentation X).groupoid.t.left).obj
        (LQCohFbc.atlasRestrict X F) ⟶
      (AlgebraicSpace.QCoh.pullback (algebraicStackPresentation X).groupoid.s.left).obj
        (LQCohFbc.atlasRestrict X F) :=
  let G := (algebraicStackPresentation X).groupoid
  let h := algebraicStackObjectSpaceHom X
  let k := algebraicStackAtlasOverToTest X
  let F0 := LQCohFbc.atlasSpaceQCoh X F
  (pullbackCompIso G.t.left h).inv.app ((AlgebraicSpace.QCoh.pullback k).obj F0) ≫
    (pullbackCompIso (G.t.left ≫ h) k).inv.app F0 ≫
      (pullbackEqIso (Category.assoc G.t.left h k)).hom.app F0 ≫
        (pullbackEqIso (algebraicStackPresentation_source_target_comp X)).hom.app F0 ≫
          (pullbackEqIso (Category.assoc G.s.left h k)).inv.app F0 ≫
            (pullbackCompIso (G.s.left ≫ h) k).hom.app F0 ≫
              (pullbackCompIso G.s.left h).hom.app ((AlgebraicSpace.QCoh.pullback k).obj F0)

/-- Descent functor `q₂` sending `F` in `LQCoh^{fbc}(𝒪_X)` to the equivariant module
`(f^* F|_{U_étale}, α)` on the chosen presentation of `X`. -/
def LQCohFbc.toGroupoidModules (X : GroupoidsOver S) [AlgebraicStack X] :
    LQCohFbc X ⥤ (algebraicStackPresentation X).groupoid.QCoh where
  obj F :=
    GroupoidAlgebraicSpace.QCoh.of (LQCohFbc.atlasRestrict X F)
      (LQCohFbc.atlasAction X F) sorry sorry
  map {F F'} f :=
    System.Hom.of
      ((AlgebraicSpace.QCoh.pullback (algebraicStackObjectSpaceHom X)).map
        ((AlgebraicSpace.QCoh.pullback (algebraicStackAtlasOverToTest X)).map
          { hom :=
              (LQCohFbc.atlasSpaceModulesLeft X).map
                (LQCohFbc.atlasSchemeModuleMap X f) }))
      sorry
  map_id := sorry
  map_comp := sorry

/-- The underlying module of `toGroupoidModules F` is the atlas restriction of `F`. -/
theorem LQCohFbc.toGroupoidModules_obj (X : GroupoidsOver S) [AlgebraicStack X]
    (F : LQCohFbc X) :
    GroupoidAlgebraicSpace.QCoh.obj ((LQCohFbc.toGroupoidModules X).obj F) =
      LQCohFbc.atlasRestrict X F :=
  rfl

/-- The equivariance map of `toGroupoidModules F` is `atlasAction`. -/
theorem LQCohFbc.toGroupoidModules_action (X : GroupoidsOver S) [AlgebraicStack X]
    (F : LQCohFbc X) :
    GroupoidAlgebraicSpace.QCoh.action ((LQCohFbc.toGroupoidModules X).obj F) =
      LQCohFbc.atlasAction X F :=
  rfl

end AlgebraicGeometry.GroupoidsOver
