module

public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import ReasLib.CategoryTheory.Sites.MorphismOfSites.Criteria
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap66.Lemma_66_16_5_Pullback
public import stacks_project.Chap66.Lemma_66_18_3_Site

/-!
# Pullback on étale sites of algebraic spaces

A morphism of algebraic spaces induces the base-change functor `V ↦ X ×_Y V` on
the étale sites of algebraic spaces, as `MorphismProperty.Over.pullback`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits CategoryTheory.MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The identity morphism as the final object of the étale site of algebraic spaces over `X`. -/
def spacesEtaleSite.self (X : AlgebraicSpace S) : spacesEtaleSite X :=
  MorphismProperty.Over.mk ⊤ (𝟙 X) inferInstance

/-- The structural morphism of `spacesEtaleSite.self X` is `𝟙 X`. -/
@[simp]
theorem spacesEtaleSite.self_hom (X : AlgebraicSpace S) :
    (spacesEtaleSite.self X).hom = 𝟙 X :=
  rfl

/-- The unique map from `V` to the final object `spacesEtaleSite.self X` is the structure
morphism `V.hom`. -/
def spacesEtaleSite.homToSelf {X : AlgebraicSpace S} (V : spacesEtaleSite X) :
    V ⟶ spacesEtaleSite.self X :=
  MorphismProperty.Over.homMk V.hom (Category.comp_id V.hom) trivial

/-- The unique map `homToSelf V` is the structure morphism `V.hom`. -/
@[simp]
theorem spacesEtaleSite.homToSelf_left {X : AlgebraicSpace S} (V : spacesEtaleSite X) :
    (spacesEtaleSite.homToSelf V).left = V.hom :=
  rfl

/-- The identity over `X` is a terminal object of `spacesEtaleSite X`. -/
def isTerminal_self (X : AlgebraicSpace S) : IsTerminal (spacesEtaleSite.self X) :=
  IsTerminal.ofUniqueHom (fun V ↦ spacesEtaleSite.homToSelf V) sorry

/-- Base change along `f` on the étale sites of algebraic spaces, sending `V` to `X ×_Y V`. -/
noncomputable abbrev spacesEtalePullback {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    spacesEtaleSite Y ⥤ spacesEtaleSite X :=
  MorphismProperty.Over.pullback (@Etale S) ⊤ f

/-- `spacesEtalePullback f` is `MorphismProperty.Over.pullback` along `f`. -/
theorem spacesEtalePullback_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    spacesEtalePullback f = MorphismProperty.Over.pullback (@Etale S) ⊤ f :=
  rfl

/-- The underlying object of `spacesEtalePullback f` on `V` is the fibre product `X ×_Y V`. -/
@[simp]
theorem spacesEtalePullback_obj_left {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : spacesEtaleSite Y) :
    ((spacesEtalePullback f).obj V).left = pullback V.hom f :=
  rfl

/-- The structural morphism of `spacesEtalePullback f` on `V` is the projection
`pullback.snd V.hom f`. -/
@[simp]
theorem spacesEtalePullback_obj_hom {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : spacesEtaleSite Y) :
    ((spacesEtalePullback f).obj V).hom = pullback.snd V.hom f :=
  rfl

/-- Base change along `f` is continuous for the étale topologies of algebraic spaces. -/
instance spacesEtalePullback_isContinuous {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (spacesEtalePullback f).IsContinuous (spacesEtaleTopology Y) (spacesEtaleTopology X) :=
  sorry

/-- Base change along `f` preserves the terminal object of the étale site of algebraic spaces. -/
instance spacesEtalePullback_preservesTerminal {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    PreservesLimit (Functor.empty.{0} (spacesEtaleSite Y)) (spacesEtalePullback f) :=
  sorry

/-- Base change along `f` preserves fibre products in the étale site of algebraic spaces. -/
instance spacesEtalePullback_preservesPullbacks {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    PreservesLimitsOfShape WalkingCospan (spacesEtalePullback f) :=
  sorry

/-- Base change along `f` is a morphism of étale sites of algebraic spaces. -/
instance spacesEtalePullback_isMorphismOfSites {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    IsMorphismOfSites (spacesEtaleTopology Y) (spacesEtaleTopology X)
      (spacesEtalePullback f) :=
  sorry

/-- Base change along a composite is the composite of the base-change functors, up to the
canonical isomorphism of chosen fibre products. -/
noncomputable def spacesEtalePullbackComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    spacesEtalePullback (f ≫ g) ≅ spacesEtalePullback g ⋙ spacesEtalePullback f :=
  MorphismProperty.Over.pullbackComp f g

/-- `spacesEtalePullbackComp f g` is `MorphismProperty.Over.pullbackComp`. -/
theorem spacesEtalePullbackComp_eq {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    spacesEtalePullbackComp f g = MorphismProperty.Over.pullbackComp f g :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
