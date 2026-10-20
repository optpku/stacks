module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import ReasLib.CategoryTheory.Sites.MorphismOfSites.Criteria
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

namespace spacesEtaleSite

/-- Every morphism to the identity étale object is the structural morphism. -/
private lemma homToSelf_unique {X : AlgebraicSpace S}
    (V : spacesEtaleSite X) (g : V ⟶ spacesEtaleSite.self X) :
    g = spacesEtaleSite.homToSelf V :=
  sorry

end spacesEtaleSite

/-- The identity over `X` is a terminal object of `spacesEtaleSite X`. -/
def isTerminal_self (X : AlgebraicSpace S) : IsTerminal (spacesEtaleSite.self X) :=
  IsTerminal.ofUniqueHom (fun V ↦ spacesEtaleSite.homToSelf V)
    (fun V g ↦ by exact spacesEtaleSite.homToSelf_unique V g)

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

/-- `spacesEtalePullbackComp f g` is `MorphismProperty.Over.pullbackComp`. -/
theorem spacesEtalePullbackComp_eq {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    spacesEtalePullbackComp f g = MorphismProperty.Over.pullbackComp f g :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
