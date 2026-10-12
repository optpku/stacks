/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Pullbacks
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite wide pullbacks and pushouts

Pullbacks construct the wide pullback of every finite family, including the empty family: the
wide-pullback diagram still contains its common codomain in that case.  The instances are exposed
at the shape level.  We deliberately do not register the aggregate reverse implication
`HasPullbacks C → HasFiniteWidePullbacks C`, because Mathlib already infers pullbacks from finite
wide pullbacks and registering both directions would create a typeclass cycle.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {J : Type w}

namespace HasWidePullback

variable {B : C} {objs : J → C} {arrows : ∀ j, objs j ⟶ B}

/-- A chosen limiting cone extracted from explicit wide-pullback existence data. -/
noncomputable def limitCone (h : HasWidePullback B objs arrows) :
    LimitCone (WidePullbackShape.wideCospan B objs arrows) :=
  Classical.choice h.exists_limit

/-- The legs opposite to a chosen wide-pullback cone satisfy the wide-pushout compatibility
condition. -/
theorem opCoconeCondition (h : HasWidePullback B objs arrows) (j : J) :
    (arrows j).op ≫ ((limitCone h).cone.π.app (some j)).op =
      ((limitCone h).cone.π.app none).op := sorry

/-- The explicit wide-pushout cocone in `Cᵒᵖ` obtained by opposing a chosen wide-pullback
cone in `C`. -/
noncomputable def opCocone (h : HasWidePullback B objs arrows) :
    Cocone (WidePushoutShape.wideSpan (Opposite.op B)
      (fun j ↦ Opposite.op (objs j)) (fun j ↦ (arrows j).op)) :=
  WidePushoutShape.mkCocone
    ((limitCone h).cone.π.app none).op
    (fun j ↦ ((limitCone h).cone.π.app (some j)).op)
    (opCoconeCondition h)

/-- The unopposite legs of a cocone over the opposite wide span satisfy the original
wide-pullback compatibility condition. -/
theorem coneOfOpCoconeCondition
    (s : Cocone (WidePushoutShape.wideSpan (Opposite.op B)
      (fun j ↦ Opposite.op (objs j)) (fun j ↦ (arrows j).op))) (j : J) :
    (s.ι.app (some j)).unop ≫ arrows j = (s.ι.app none).unop := sorry

/-- A cocone over the opposite wide span gives a cone over the original wide cospan. -/
noncomputable def coneOfOpCocone
    (s : Cocone (WidePushoutShape.wideSpan (Opposite.op B)
      (fun j ↦ Opposite.op (objs j)) (fun j ↦ (arrows j).op))) :
    Cone (WidePullbackShape.wideCospan B objs arrows) :=
  WidePullbackShape.mkCone (s.ι.app none).unop
    (fun j ↦ (s.ι.app (some j)).unop) (coneOfOpCoconeCondition s)

/-- The descent map for the opposite cocone is the opposite of the original limiting lift. -/
noncomputable def opDesc (h : HasWidePullback B objs arrows)
    (s : Cocone (WidePushoutShape.wideSpan (Opposite.op B)
      (fun j ↦ Opposite.op (objs j)) (fun j ↦ (arrows j).op))) :
    (opCocone h).pt ⟶ s.pt :=
  ((limitCone h).isLimit.lift (coneOfOpCocone s)).op

/-- The opposite descent map commutes with every cocone leg. -/
theorem opDescFac (h : HasWidePullback B objs arrows)
    (s : Cocone (WidePushoutShape.wideSpan (Opposite.op B)
      (fun j ↦ Opposite.op (objs j)) (fun j ↦ (arrows j).op)))
    (j : WidePushoutShape J) :
    (opCocone h).ι.app j ≫ opDesc h s = s.ι.app j := sorry

/-- The opposite descent map is uniquely determined by its composites with the cocone legs. -/
theorem opDescUniq (h : HasWidePullback B objs arrows)
    (s : Cocone (WidePushoutShape.wideSpan (Opposite.op B)
      (fun j ↦ Opposite.op (objs j)) (fun j ↦ (arrows j).op)))
    (m : (opCocone h).pt ⟶ s.pt)
    (hm : ∀ j, (opCocone h).ι.app j ≫ m = s.ι.app j) :
    m = opDesc h s := sorry

/-- The cocone obtained by opposing a limiting wide-pullback cone is colimiting. -/
noncomputable def opCoconeIsColimit (h : HasWidePullback B objs arrows) :
    IsColimit (opCocone h) where
  desc := opDesc h
  fac := opDescFac h
  uniq := opDescUniq h

/-- Opposing explicit wide-pullback existence data gives explicit wide-pushout existence data. -/
@[stacks 019Z "opposite wide-pullback existence bridge"]
noncomputable def op (h : HasWidePullback B objs arrows) :
    HasWidePushout (Opposite.op B)
      (fun j ↦ Opposite.op (objs j)) (fun j ↦ (arrows j).op) :=
  HasColimit.mk { cocone := opCocone h, isColimit := opCoconeIsColimit h }

section Unop

variable {B : Cᵒᵖ} {objs : J → Cᵒᵖ} {arrows : ∀ j, objs j ⟶ B}

/-- The unopposite legs of a chosen wide-pullback cone satisfy the wide-pushout compatibility
condition. -/
theorem unopCoconeCondition (h : HasWidePullback B objs arrows) (j : J) :
    (arrows j).unop ≫ ((limitCone h).cone.π.app (some j)).unop =
      ((limitCone h).cone.π.app none).unop := sorry

/-- The explicit wide-pushout cocone in `C` obtained by unopposing a chosen wide-pullback cone
in `Cᵒᵖ`. -/
noncomputable def unopCocone (h : HasWidePullback B objs arrows) :
    Cocone (WidePushoutShape.wideSpan (Opposite.unop B)
      (fun j ↦ Opposite.unop (objs j)) (fun j ↦ (arrows j).unop)) :=
  WidePushoutShape.mkCocone
    ((limitCone h).cone.π.app none).unop
    (fun j ↦ ((limitCone h).cone.π.app (some j)).unop)
    (unopCoconeCondition h)

/-- The opposite legs of a cocone over the unopposite wide span satisfy the original
wide-pullback compatibility condition. -/
theorem coneOfUnopCoconeCondition
    (s : Cocone (WidePushoutShape.wideSpan (Opposite.unop B)
      (fun j ↦ Opposite.unop (objs j)) (fun j ↦ (arrows j).unop))) (j : J) :
    (s.ι.app (some j)).op ≫ arrows j = (s.ι.app none).op := sorry

/-- A cocone over the unopposite wide span gives a cone over the original wide cospan. -/
noncomputable def coneOfUnopCocone
    (s : Cocone (WidePushoutShape.wideSpan (Opposite.unop B)
      (fun j ↦ Opposite.unop (objs j)) (fun j ↦ (arrows j).unop))) :
    Cone (WidePullbackShape.wideCospan B objs arrows) :=
  WidePullbackShape.mkCone (s.ι.app none).op
    (fun j ↦ (s.ι.app (some j)).op) (coneOfUnopCoconeCondition s)

/-- The descent map for the unopposite cocone is the unopposite of the original limiting lift. -/
noncomputable def unopDesc (h : HasWidePullback B objs arrows)
    (s : Cocone (WidePushoutShape.wideSpan (Opposite.unop B)
      (fun j ↦ Opposite.unop (objs j)) (fun j ↦ (arrows j).unop))) :
    (unopCocone h).pt ⟶ s.pt :=
  ((limitCone h).isLimit.lift (coneOfUnopCocone s)).unop

/-- The unopposite descent map commutes with every cocone leg. -/
theorem unopDescFac (h : HasWidePullback B objs arrows)
    (s : Cocone (WidePushoutShape.wideSpan (Opposite.unop B)
      (fun j ↦ Opposite.unop (objs j)) (fun j ↦ (arrows j).unop)))
    (j : WidePushoutShape J) :
    (unopCocone h).ι.app j ≫ unopDesc h s = s.ι.app j := sorry

/-- The unopposite descent map is uniquely determined by its composites with the cocone legs. -/
theorem unopDescUniq (h : HasWidePullback B objs arrows)
    (s : Cocone (WidePushoutShape.wideSpan (Opposite.unop B)
      (fun j ↦ Opposite.unop (objs j)) (fun j ↦ (arrows j).unop)))
    (m : (unopCocone h).pt ⟶ s.pt)
    (hm : ∀ j, (unopCocone h).ι.app j ≫ m = s.ι.app j) :
    m = unopDesc h s := sorry

/-- The cocone obtained by unopposing a limiting wide-pullback cone is colimiting. -/
noncomputable def unopCoconeIsColimit (h : HasWidePullback B objs arrows) :
    IsColimit (unopCocone h) where
  desc := unopDesc h
  fac := unopDescFac h
  uniq := unopDescUniq h

/-- Unopposing explicit wide-pullback existence data gives explicit wide-pushout existence data. -/
@[stacks 019Z "unopposite wide-pullback existence bridge"]
noncomputable def unop (h : HasWidePullback B objs arrows) :
    HasWidePushout (Opposite.unop B)
      (fun j ↦ Opposite.unop (objs j)) (fun j ↦ (arrows j).unop) :=
  HasColimit.mk { cocone := unopCocone h, isColimit := unopCoconeIsColimit h }

end Unop

end HasWidePullback

namespace HasWidePushout

variable {B : C} {objs : J → C} {arrows : ∀ j, B ⟶ objs j}

/-- A chosen colimiting cocone extracted from explicit wide-pushout existence data. -/
noncomputable def colimitCocone (h : HasWidePushout B objs arrows) :
    ColimitCocone (WidePushoutShape.wideSpan B objs arrows) :=
  Classical.choice h.exists_colimit

/-- The legs opposite to a chosen wide-pushout cocone satisfy the wide-pullback compatibility
condition. -/
theorem opConeCondition (h : HasWidePushout B objs arrows) (j : J) :
    ((colimitCocone h).cocone.ι.app (some j)).op ≫ (arrows j).op =
      ((colimitCocone h).cocone.ι.app none).op := sorry

/-- The explicit wide-pullback cone in `Cᵒᵖ` obtained by opposing a chosen wide-pushout
cocone in `C`. -/
noncomputable def opCone (h : HasWidePushout B objs arrows) :
    Cone (WidePullbackShape.wideCospan (Opposite.op B)
      (fun j ↦ Opposite.op (objs j)) (fun j ↦ (arrows j).op)) :=
  WidePullbackShape.mkCone
    ((colimitCocone h).cocone.ι.app none).op
    (fun j ↦ ((colimitCocone h).cocone.ι.app (some j)).op)
    (opConeCondition h)

/-- The unopposite legs of a cone over the opposite wide cospan satisfy the original
wide-pushout compatibility condition. -/
theorem coconeOfOpConeCondition
    (s : Cone (WidePullbackShape.wideCospan (Opposite.op B)
      (fun j ↦ Opposite.op (objs j)) (fun j ↦ (arrows j).op))) (j : J) :
    arrows j ≫ (s.π.app (some j)).unop = (s.π.app none).unop := sorry

/-- A cone over the opposite wide cospan gives a cocone over the original wide span. -/
noncomputable def coconeOfOpCone
    (s : Cone (WidePullbackShape.wideCospan (Opposite.op B)
      (fun j ↦ Opposite.op (objs j)) (fun j ↦ (arrows j).op))) :
    Cocone (WidePushoutShape.wideSpan B objs arrows) :=
  WidePushoutShape.mkCocone (s.π.app none).unop
    (fun j ↦ (s.π.app (some j)).unop) (coconeOfOpConeCondition s)

/-- The lift into the opposite cone is the opposite of the original colimiting descent map. -/
noncomputable def opLift (h : HasWidePushout B objs arrows)
    (s : Cone (WidePullbackShape.wideCospan (Opposite.op B)
      (fun j ↦ Opposite.op (objs j)) (fun j ↦ (arrows j).op))) :
    s.pt ⟶ (opCone h).pt :=
  ((colimitCocone h).isColimit.desc (coconeOfOpCone s)).op

/-- The opposite lift commutes with every cone leg. -/
theorem opLiftFac (h : HasWidePushout B objs arrows)
    (s : Cone (WidePullbackShape.wideCospan (Opposite.op B)
      (fun j ↦ Opposite.op (objs j)) (fun j ↦ (arrows j).op)))
    (j : WidePullbackShape J) :
    opLift h s ≫ (opCone h).π.app j = s.π.app j := sorry

/-- The opposite lift is uniquely determined by its composites with the cone legs. -/
theorem opLiftUniq (h : HasWidePushout B objs arrows)
    (s : Cone (WidePullbackShape.wideCospan (Opposite.op B)
      (fun j ↦ Opposite.op (objs j)) (fun j ↦ (arrows j).op)))
    (m : s.pt ⟶ (opCone h).pt)
    (hm : ∀ j, m ≫ (opCone h).π.app j = s.π.app j) :
    m = opLift h s := sorry

/-- The cone obtained by opposing a colimiting wide-pushout cocone is limiting. -/
noncomputable def opConeIsLimit (h : HasWidePushout B objs arrows) :
    IsLimit (opCone h) where
  lift := opLift h
  fac := opLiftFac h
  uniq := opLiftUniq h

/-- Opposing explicit wide-pushout existence data gives explicit wide-pullback existence data. -/
@[stacks 019Z "opposite wide-pushout existence bridge"]
noncomputable def op (h : HasWidePushout B objs arrows) :
    HasWidePullback (Opposite.op B)
      (fun j ↦ Opposite.op (objs j)) (fun j ↦ (arrows j).op) :=
  HasLimit.mk { cone := opCone h, isLimit := opConeIsLimit h }

section Unop

variable {B : Cᵒᵖ} {objs : J → Cᵒᵖ} {arrows : ∀ j, B ⟶ objs j}

/-- The unopposite legs of a chosen wide-pushout cocone satisfy the wide-pullback compatibility
condition. -/
theorem unopConeCondition (h : HasWidePushout B objs arrows) (j : J) :
    ((colimitCocone h).cocone.ι.app (some j)).unop ≫ (arrows j).unop =
      ((colimitCocone h).cocone.ι.app none).unop := sorry

/-- The explicit wide-pullback cone in `C` obtained by unopposing a chosen wide-pushout cocone
in `Cᵒᵖ`. -/
noncomputable def unopCone (h : HasWidePushout B objs arrows) :
    Cone (WidePullbackShape.wideCospan (Opposite.unop B)
      (fun j ↦ Opposite.unop (objs j)) (fun j ↦ (arrows j).unop)) :=
  WidePullbackShape.mkCone
    ((colimitCocone h).cocone.ι.app none).unop
    (fun j ↦ ((colimitCocone h).cocone.ι.app (some j)).unop)
    (unopConeCondition h)

/-- The opposite legs of a cone over the unopposite wide cospan satisfy the original
wide-pushout compatibility condition. -/
theorem coconeOfUnopConeCondition
    (s : Cone (WidePullbackShape.wideCospan (Opposite.unop B)
      (fun j ↦ Opposite.unop (objs j)) (fun j ↦ (arrows j).unop))) (j : J) :
    arrows j ≫ (s.π.app (some j)).op = (s.π.app none).op := sorry

/-- A cone over the unopposite wide cospan gives a cocone over the original wide span. -/
noncomputable def coconeOfUnopCone
    (s : Cone (WidePullbackShape.wideCospan (Opposite.unop B)
      (fun j ↦ Opposite.unop (objs j)) (fun j ↦ (arrows j).unop))) :
    Cocone (WidePushoutShape.wideSpan B objs arrows) :=
  WidePushoutShape.mkCocone (s.π.app none).op
    (fun j ↦ (s.π.app (some j)).op) (coconeOfUnopConeCondition s)

/-- The lift into the unopposite cone is the unopposite of the original colimiting descent map. -/
noncomputable def unopLift (h : HasWidePushout B objs arrows)
    (s : Cone (WidePullbackShape.wideCospan (Opposite.unop B)
      (fun j ↦ Opposite.unop (objs j)) (fun j ↦ (arrows j).unop))) :
    s.pt ⟶ (unopCone h).pt :=
  ((colimitCocone h).isColimit.desc (coconeOfUnopCone s)).unop

/-- The unopposite lift commutes with every cone leg. -/
theorem unopLiftFac (h : HasWidePushout B objs arrows)
    (s : Cone (WidePullbackShape.wideCospan (Opposite.unop B)
      (fun j ↦ Opposite.unop (objs j)) (fun j ↦ (arrows j).unop)))
    (j : WidePullbackShape J) :
    unopLift h s ≫ (unopCone h).π.app j = s.π.app j := sorry

/-- The unopposite lift is uniquely determined by its composites with the cone legs. -/
theorem unopLiftUniq (h : HasWidePushout B objs arrows)
    (s : Cone (WidePullbackShape.wideCospan (Opposite.unop B)
      (fun j ↦ Opposite.unop (objs j)) (fun j ↦ (arrows j).unop)))
    (m : s.pt ⟶ (unopCone h).pt)
    (hm : ∀ j, m ≫ (unopCone h).π.app j = s.π.app j) :
    m = unopLift h s := sorry

/-- The cone obtained by unopposing a colimiting wide-pushout cocone is limiting. -/
noncomputable def unopConeIsLimit (h : HasWidePushout B objs arrows) :
    IsLimit (unopCone h) where
  lift := unopLift h
  fac := unopLiftFac h
  uniq := unopLiftUniq h

/-- Unopposing explicit wide-pushout existence data gives explicit wide-pullback existence data. -/
@[stacks 019Z "unopposite wide-pushout existence bridge"]
noncomputable def unop (h : HasWidePushout B objs arrows) :
    HasWidePullback (Opposite.unop B)
      (fun j ↦ Opposite.unop (objs j)) (fun j ↦ (arrows j).unop) :=
  HasLimit.mk { cone := unopCone h, isLimit := unopConeIsLimit h }

end Unop

end HasWidePushout

namespace HasPullbacks

namespace WidePullback

/-- Pullbacks give binary products in every slice, and the identity over the base gives the
terminal object, hence every slice has finite products. -/
@[stacks 018I "finite products in a slice from pullbacks"]
def overFiniteProducts (B : C) [HasPullbacks C] : HasFiniteProducts (Over B) :=
  @CategoryTheory.hasFiniteProducts_of_has_binary_and_terminal
    (Over B) _
    (Over.ConstructProducts.over_binaryProduct_of_pullback (C := C) (B := B))
    (Over.over_hasTerminal B)

/-- The finite-product existence data in a slice, specialized to an arbitrary finite indexing
type. -/
@[stacks 018I "finite products of arbitrary finite shape in a slice"]
def overFiniteShape (B : C) [HasPullbacks C] [Finite J] :
    HasLimitsOfShape (Discrete J) (Over B) :=
  @hasLimitsOfShape_discrete (Over B) _ (overFiniteProducts B) J _

/-- The discrete diagram in the slice whose objects are the spokes of a wide-pullback-shaped
diagram. -/
@[stacks 018I "slice diagram of wide-pullback spokes"]
def spokes (F : WidePullbackShape J ⥤ C) : Discrete J ⥤ Over (F.obj none) :=
  Discrete.functor fun j ↦ Over.mk (F.map (WidePullbackShape.Hom.term j))

/-- A chosen finite-product cone on the spokes of a finite wide-pullback-shaped diagram. -/
noncomputable def productCone [HasPullbacks C] [Finite J]
    (F : WidePullbackShape J ⥤ C) : LimitCone (spokes F) :=
  Classical.choice
    ((overFiniteShape (J := J) (F.obj none)).has_limit (spokes F)).exists_limit

/-- The finite-product cone on the spokes, regarded as a cone on the normalized wide cospan. -/
noncomputable def normalizedCone [HasPullbacks C] [Finite J]
    (F : WidePullbackShape J ⥤ C) :
    Cone (WidePullbackShape.wideCospan (F.obj none)
      (fun j ↦ F.obj (some j)) (fun j ↦ F.map (WidePullbackShape.Hom.term j))) :=
  Over.ConstructProducts.conesEquivInverseObj
    (F.obj none) (spokes F) (productCone F).cone

/-- The normalized cone is limiting because the cone equivalence sends finite products in the
slice to wide pullbacks in the ambient category. -/
noncomputable def normalizedConeIsLimit [HasPullbacks C] [Finite J]
    (F : WidePullbackShape J ⥤ C) : IsLimit (normalizedCone F) :=
  IsLimit.ofRightAdjoint
    (Over.ConstructProducts.conesEquiv (F.obj none) (spokes F)).toAdjunction
    (productCone F).isLimit

/-- The chosen cone on an arbitrary finite wide-pullback-shaped diagram, transported from its
normalized wide cospan. -/
@[stacks 018I "chosen finite wide-pullback cone from pullbacks"]
noncomputable def cone [HasPullbacks C] [Finite J]
    (F : WidePullbackShape J ⥤ C) : Cone F :=
  (Cone.postcompose (WidePullbackShape.diagramIsoWideCospan F).inv).obj
    (normalizedCone F)

/-- The chosen finite wide-pullback cone constructed from pullbacks is limiting. -/
noncomputable def coneIsLimit [HasPullbacks C] [Finite J]
    (F : WidePullbackShape J ⥤ C) : IsLimit (cone F) :=
  (IsLimit.postcomposeInvEquiv
    (WidePullbackShape.diagramIsoWideCospan F) (normalizedCone F)).symm
      (normalizedConeIsLimit F)

/-- The explicit limit cone owner for a finite wide-pullback-shaped diagram in a category with
pullbacks. -/
@[stacks 018I "finite wide-pullback limit cone from pullbacks"]
noncomputable def limitCone [HasPullbacks C] [Finite J]
  (F : WidePullbackShape J ⥤ C) : LimitCone F where
  cone := cone F
  isLimit := coneIsLimit F

end WidePullback

/-- Every finite wide-pullback-shaped diagram has a limit whenever the ambient category has
pullbacks. -/
@[stacks 018I "finite wide pullbacks from pullbacks"]
instance (priority := 100) widePullbackShape [HasPullbacks C] [Finite J] :
    HasLimitsOfShape (WidePullbackShape J) C where
  has_limit F := HasLimit.mk (WidePullback.limitCone F)

end HasPullbacks

namespace HasPushouts

namespace WidePushout

/-- Finite wide-pullback limits in the opposite category, reindexed by the wide-shape duality. -/
@[stacks 016N "opposite finite wide-pullback limits for wide pushouts"]
def oppositeLimits [HasPushouts C] [Finite J] :
    HasLimitsOfShape (WidePushoutShape J)ᵒᵖ Cᵒᵖ :=
  hasLimitsOfShape_of_equivalence (widePushoutShapeOpEquiv J).symm

end WidePushout

/-- Every finite wide-pushout-shaped diagram has a colimit whenever the ambient category has
pushouts. -/
@[stacks 016N "finite wide pushouts from pushouts"]
instance (priority := 100) widePushoutShape [HasPushouts C] [Finite J] :
    HasColimitsOfShape (WidePushoutShape J) C where
  has_colimit F :=
    @hasColimit_of_hasLimit_op (C := C) _ (J := WidePushoutShape J) _ F
      ((WidePushout.oppositeLimits (C := C) (J := J)).has_limit F.op)

end HasPushouts

end CategoryTheory.Limits
