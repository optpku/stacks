module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GaloisPullback.ResidualGerbe
import StacksCheckRecall

/-!
# A one-point non-Noetherian algebraic space

The quotient of the algebraic-closure pullback by the discrete absolute Galois
group is reduced and has one point. Its canonical field-valued point is a
locally finite type monomorphism and its residual gerbe, but is not an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace.GaloisPullback
open AlgebraicGeometry.Scheme.PreRelation
open FiberedCategoryOver
open FiberedCategoryOver.Groupoids (toFunctor overMap)
open scoped Bicategory

/- Example 100.11.6: the canonical field-spectrum point of the Galois pullback
quotient is not an isomorphism. -/
@[stacks 06MS] #check
  (AlgebraicGeometry.AlgebraicSpace.GaloisPullback.not_isEquivalence_pointHom :
    ¬ (FiberedCategoryOver.Groupoids.toBasedFunctor
      AlgebraicGeometry.AlgebraicSpace.GaloisPullback.pointHom).IsEquivalence)

#check (base_eq : base = Spec (CommRingCat.of AlgebraicNumbers.algebraicQ))
#check (cover_left : cover.left = pullback specMapQ specMapQ)
#check (cover_hom : cover.hom = pullback.snd specMapQ specMapQ)
#check (constantGroup_eq :
  constantGroup = ConstantGroup.baseChange base (GrpCat.of AlgebraicNumbers.gal))
#check (action_apply_eq_iff : ∀ (σ : AlgebraicNumbers.gal) (u : cover.left),
  (action σ).hom.left u = u ↔ σ = 1)
#check (instIsResidueFieldFree_action : IsResidueFieldFree action)
#check (exists_action_eq : ∀ (u v : cover.left),
  ∃ σ : AlgebraicNumbers.gal, (action σ).hom.left u = v)
#check (mem_closedPoints_cover : ∀ (u : cover.left), u ∈ closedPoints cover.left)
#check (sheafOfPoints_eq :
  sheafOfPoints = (ofAut action).quotientSheaf (Scheme.fppfTopology.over base))
#check (sheafOfPoints_spec :
  uliftYoneda.{1}.relativelyRepresentable (diag sheafOfPoints.obj) ∧
    (MorphismProperty.over (@Etale)).relative uliftYoneda.{1} atlas.hom ∧
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over base) atlas.hom)
#check (pointHom_eq : pointHom = overMap sectionHom ≫ sliceToCover ≫ atlasHom)
#check (xPoint_eq :
  xPoint = AlgebraicStack.Points.mk
    (AlgebraicStack.FieldValuedPoint.of AlgebraicNumbers.algebraicQ (𝟙 base) pointHom))
#check (instAlgebraicStack_toStack : AlgebraicStack toStack)
#check (instIsReduced_toStack : AlgebraicStack.IsReduced toStack)
#check (instNonempty_points_toStack : Nonempty (AlgebraicStack.Points toStack))
#check (instSubsingleton_points_toStack : Subsingleton (AlgebraicStack.Points toStack))
#check (not_isLocallyNoetherian : ¬ AlgebraicStack.IsLocallyNoetherian toStack)
#check (instLocallyOfFiniteType_pointHom : Groupoids.Hom.LocallyOfFiniteType pointHom)
#check (isFiniteTypePoint_xPoint : AlgebraicStack.IsFiniteTypePoint xPoint)
#check (instMono_pointHom : Groupoids.Hom.Mono pointHom)
#check (AlgebraicStack.instHasResidualGerbe_of_subsingleton_points toStack :
  AlgebraicStack.HasResidualGerbe toStack xPoint)
#check (instIsResidualGerbe_pointHom : AlgebraicStack.IsResidualGerbe pointHom xPoint)
#check (pointHom_essImage_eq_residualGerbeι :
  (toFunctor pointHom).essImage =
    (toFunctor (AlgebraicStack.residualGerbeι toStack xPoint)).essImage)
