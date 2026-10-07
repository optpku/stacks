module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import stacks_project.Chap07.Definition_7_6_2_Site
public import stacks_project.Chap07.Definition_7_14_1
public import stacks_project.Chap66.Lemma_66_18_8_Pullback

/-!
# Spaces-étale total site of a simplicial algebraic space

Objects of `SpacesEtale U` are algebraic spaces étale over some stage `U.obj n`.
A morphism is a commutative square: a simplex operator together with a map of
algebraic spaces over the corresponding structure map of `U`. Coverings are the
identity-degree étale covers of Section 85.32.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Simplicial MorphismOfTopoiIn

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

/-- An object of the spaces-étale site of a simplicial algebraic space `U`: an
algebraic space étale over some stage `U.obj n`. -/
structure SpacesEtale {S : Scheme.{u}} (U : SimplicialObject (AlgebraicSpace S)) where
  /-- The simplicial degree `n` such that the object lives over `U.obj n`. -/
  index : SimplexCategoryᵒᵖ
  /-- An algebraic space étale over `U.obj index`. -/
  obj : spacesEtaleSite (U.obj index)

namespace SpacesEtale

variable {S : Scheme.{u}} {U : SimplicialObject (AlgebraicSpace S)}

/-- A morphism `Y ⟶ Z` in `SpacesEtale U` is a commutative square: a simplex
operator `φ : Z.index.unop ⟶ Y.index.unop` and a map of algebraic spaces
`Y.obj.left ⟶ Z.obj.left` over `U.map φ.op`. -/
structure Hom (Y Z : SpacesEtale U) where
  /-- The underlying simplex operator `φ : Z.index.unop ⟶ Y.index.unop`. -/
  simplex : Z.index.unop ⟶ Y.index.unop
  /-- The map of algebraic spaces `Y.obj.left ⟶ Z.obj.left`. -/
  hom : Y.obj.left ⟶ Z.obj.left
  /-- The square commutes: `hom ≫ Z.obj.hom = Y.obj.hom ≫ U.map simplex.op`. -/
  w : hom ≫ Z.obj.hom = Y.obj.hom ≫ U.map simplex.op

/-- The object of `SpacesEtale U` given by an étale algebraic space over `U.obj n`. -/
def ofStage (n : SimplexCategoryᵒᵖ) (V : spacesEtaleSite (U.obj n)) : SpacesEtale U where
  index := n
  obj := V

/-- The simplicial degree of `ofStage n V` is `n`. -/
theorem ofStage_index (n : SimplexCategoryᵒᵖ) (V : spacesEtaleSite (U.obj n)) :
    (ofStage n V).index = n :=
  rfl

/-- The underlying étale object of `ofStage n V` is `V`. -/
theorem ofStage_obj (n : SimplexCategoryᵒᵖ) (V : spacesEtaleSite (U.obj n)) :
    (ofStage n V).obj = V :=
  rfl

/-- Build a morphism of `SpacesEtale U` from a commutative square. -/
def homMk {Y Z : SpacesEtale U} (simplex : Z.index.unop ⟶ Y.index.unop)
    (hom : Y.obj.left ⟶ Z.obj.left)
    (w : hom ≫ Z.obj.hom = Y.obj.hom ≫ U.map simplex.op) : Hom Y Z where
  simplex := simplex
  hom := hom
  w := w

/-- The simplex operator of `homMk simplex hom w` is `simplex`. -/
theorem homMk_simplex {Y Z : SpacesEtale U} (simplex : Z.index.unop ⟶ Y.index.unop)
    (hom : Y.obj.left ⟶ Z.obj.left)
    (w : hom ≫ Z.obj.hom = Y.obj.hom ≫ U.map simplex.op) :
    (homMk simplex hom w).simplex = simplex :=
  rfl

/-- The underlying map of `homMk simplex hom w` is `hom`. -/
theorem homMk_hom {Y Z : SpacesEtale U} (simplex : Z.index.unop ⟶ Y.index.unop)
    (hom : Y.obj.left ⟶ Z.obj.left)
    (w : hom ≫ Z.obj.hom = Y.obj.hom ≫ U.map simplex.op) :
    (homMk simplex hom w).hom = hom :=
  rfl

/-- The identity simplex operator satisfies the commutativity condition. -/
theorem Hom.id_w (Y : SpacesEtale U) :
    𝟙 Y.obj.left ≫ Y.obj.hom = Y.obj.hom ≫ U.map (𝟙 Y.index.unop).op :=
  sorry

/-- The identity morphism of an object of `SpacesEtale U`. -/
def Hom.id (Y : SpacesEtale U) : Hom Y Y :=
  homMk (𝟙 Y.index.unop) (𝟙 Y.obj.left) (Hom.id_w Y)

/-- Composite simplex operators satisfy the commutativity condition. -/
theorem Hom.comp_w {Y Z W : SpacesEtale U} (f : Hom Y Z) (g : Hom Z W) :
    (f.hom ≫ g.hom) ≫ W.obj.hom =
      Y.obj.hom ≫ U.map (g.simplex ≫ f.simplex).op :=
  sorry

/-- Composition of morphisms of `SpacesEtale U` composes simplex operators and
underlying maps. -/
def Hom.comp {Y Z W : SpacesEtale U} (f : Hom Y Z) (g : Hom Z W) : Hom Y W :=
  homMk (g.simplex ≫ f.simplex) (f.hom ≫ g.hom) (Hom.comp_w f g)

/-- Left identity for morphisms of `SpacesEtale U`. -/
theorem Hom.id_comp {Y Z : SpacesEtale U} (f : Hom Y Z) :
    Hom.comp (Hom.id Y) f = f :=
  sorry

/-- Right identity for morphisms of `SpacesEtale U`. -/
theorem Hom.comp_id {Y Z : SpacesEtale U} (f : Hom Y Z) :
    Hom.comp f (Hom.id Z) = f :=
  sorry

/-- Associativity for morphisms of `SpacesEtale U`. -/
theorem Hom.assoc {Y Z W V : SpacesEtale U} (f : Hom Y Z) (g : Hom Z W) (h : Hom W V) :
    Hom.comp (Hom.comp f g) h = Hom.comp f (Hom.comp g h) :=
  sorry

/-- The category of algebraic spaces étale over the stages of `U`. -/
instance category : Category.{u + 1} (SpacesEtale U) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- Identity-simplex morphisms of `SpacesEtale U` satisfy the commutativity
condition. -/
theorem homOfStage_w {n : SimplexCategoryᵒᵖ} {V W : spacesEtaleSite (U.obj n)}
    (f : V ⟶ W) :
    f.left ≫ W.hom = V.hom ≫ U.map (𝟙 n.unop).op :=
  sorry

/-- The identity-simplex morphism of `SpacesEtale U` associated to a morphism of
étale objects over a fixed stage. -/
def homOfStage {n : SimplexCategoryᵒᵖ} {V W : spacesEtaleSite (U.obj n)} (f : V ⟶ W) :
    ofStage n V ⟶ ofStage n W :=
  homMk (𝟙 n.unop) f.left (homOfStage_w f)

/-- The functor sending an étale object over `U.obj n` to the corresponding object
of `SpacesEtale U` on the identity simplex. -/
def includeStage (n : SimplexCategoryᵒᵖ) : spacesEtaleSite (U.obj n) ⥤ SpacesEtale U where
  obj V := ofStage n V
  map f := homOfStage f
  map_id := sorry
  map_comp := sorry

/-- `includeStage n` sends `V` to `ofStage n V`. -/
theorem includeStage_obj (n : SimplexCategoryᵒᵖ) (V : spacesEtaleSite (U.obj n)) :
    (includeStage n).obj V = ofStage n V :=
  rfl

/-- The adjunct of a commutative-square morphism as a map into the pullback along
the structure map of `U`. -/
def homEquivToPullback {Y Z : SpacesEtale U} (f : Y ⟶ Z) :
    Y.obj ⟶ (spacesEtalePullback (U.map f.simplex.op)).obj Z.obj :=
  MorphismProperty.Over.homMk
    (pullback.lift f.hom Y.obj.hom f.w)
    (pullback.lift_snd f.hom Y.obj.hom f.w) trivial

/-- Rebuilding a commutative-square morphism from a pullback-hom. -/
theorem homEquivFromPullback_w {Y Z : SpacesEtale U} (φ : Z.index.unop ⟶ Y.index.unop)
    (g : Y.obj ⟶ (spacesEtalePullback (U.map φ.op)).obj Z.obj) :
    (g.left ≫ pullback.fst Z.obj.hom (U.map φ.op)) ≫ Z.obj.hom =
      Y.obj.hom ≫ U.map φ.op :=
  sorry

/-- The commutative-square morphism associated to a simplex operator and a
pullback-hom. -/
def homEquivFromPullback {Y Z : SpacesEtale U} (φ : Z.index.unop ⟶ Y.index.unop)
    (g : Y.obj ⟶ (spacesEtalePullback (U.map φ.op)).obj Z.obj) : Y ⟶ Z :=
  homMk φ (g.left ≫ pullback.fst Z.obj.hom (U.map φ.op)) (homEquivFromPullback_w φ g)

/-- `homEquivFromPullback` recovers a commutative-square morphism from its adjunct. -/
theorem homEquiv_left_inv {Y Z : SpacesEtale U} (f : Y ⟶ Z) :
    homEquivFromPullback f.simplex (homEquivToPullback f) = f :=
  sorry

/-- `homEquivToPullback` recovers a pullback-hom from the rebuilt square. -/
theorem homEquiv_right_inv {Y Z : SpacesEtale U} (φ : Z.index.unop ⟶ Y.index.unop)
    (g : Y.obj ⟶ (spacesEtalePullback (U.map φ.op)).obj Z.obj) :
    homEquivToPullback (homEquivFromPullback φ g) = g :=
  sorry

/-- Morphisms `Y ⟶ Z` in `SpacesEtale U` are equivalently a simplex operator
`φ : Z.index.unop ⟶ Y.index.unop` together with a morphism
`Y.obj ⟶ (spacesEtalePullback (U.map φ.op)).obj Z.obj` over `U.obj Y.index`. -/
def homEquiv {Y Z : SpacesEtale U} :
    (Y ⟶ Z) ≃
      Σ φ : Z.index.unop ⟶ Y.index.unop,
        Y.obj ⟶ (spacesEtalePullback (U.map φ.op)).obj Z.obj where
  toFun f := ⟨f.simplex, homEquivToPullback f⟩
  invFun p := homEquivFromPullback p.1 p.2
  left_inv := sorry
  right_inv := sorry

/-- `homEquiv` unpacks a morphism as its simplex operator and adjunct pullback-hom. -/
theorem homEquiv_apply {Y Z : SpacesEtale U} (f : Y ⟶ Z) :
    homEquiv f = ⟨f.simplex, homEquivToPullback f⟩ :=
  rfl

/-- The simplex operator extracted by `homEquiv` is `f.simplex`. -/
theorem homEquiv_simplex {Y Z : SpacesEtale U} (f : Y ⟶ Z) :
    (homEquiv f).1 = f.simplex :=
  rfl

/-- Identity-degree covering families in `SpacesEtale U` are the images of stage
étale covering families under `includeStage`. -/
def ofStageArrows {Y : SpacesEtale U} {I : Type u} (V : I → spacesEtaleSite (U.obj Y.index))
    (p : ∀ i, V i ⟶ Y.obj) : Presieve Y :=
  Presieve.ofArrows (fun i ↦ ofStage Y.index (V i)) (fun i ↦ homOfStage (p i))

end SpacesEtale

variable {S : Scheme.{u}} (U : SimplicialObject (AlgebraicSpace S))

/-- Identity-degree covering families in `SpacesEtale U`, transported from the
spaces-étale precoverage of the corresponding stage. -/
def spacesEtaleTotalPrecoverage : Precoverage (SpacesEtale U) where
  coverings Y :=
    { R |
        ∃ (I : Type u) (_ : Small.{u} I) (V : I → spacesEtaleSite (U.obj Y.index))
          (p : ∀ i, V i ⟶ Y.obj),
          R = SpacesEtale.ofStageArrows V p ∧
            Presieve.ofArrows V p ∈ spacesEtalePrecoverage (U.obj Y.index) Y.obj }

/-- A presieve covers in `spacesEtaleTotalPrecoverage U` iff it is the identity-degree
image of a spaces-étale covering of the underlying stage object. -/
theorem mem_spacesEtaleTotalPrecoverage_iff {Y : SpacesEtale U} {R : Presieve Y} :
    R ∈ spacesEtaleTotalPrecoverage U Y ↔
      ∃ (I : Type u) (_ : Small.{u} I) (V : I → spacesEtaleSite (U.obj Y.index))
        (p : ∀ i, V i ⟶ Y.obj),
        R = SpacesEtale.ofStageArrows V p ∧
          Presieve.ofArrows V p ∈ spacesEtalePrecoverage (U.obj Y.index) Y.obj :=
  sorry

/-- An identity-degree family covers in `spacesEtaleTotalPrecoverage U` iff the
underlying stage family covers. -/
theorem ofStageArrows_mem_spacesEtaleTotalPrecoverage_iff {Y : SpacesEtale U}
    {I : Type u} [Small.{u} I] (V : I → spacesEtaleSite (U.obj Y.index))
    (p : ∀ i, V i ⟶ Y.obj) :
    SpacesEtale.ofStageArrows V p ∈ spacesEtaleTotalPrecoverage U Y ↔
      Presieve.ofArrows V p ∈ spacesEtalePrecoverage (U.obj Y.index) Y.obj :=
  sorry

/-- Identity-degree étale covers of the stages of `U` satisfy the site axioms. -/
instance spacesEtaleTotalPrecoverage.instIsSite : (spacesEtaleTotalPrecoverage U).IsSite :=
  sorry

/-- The Grothendieck topology on `SpacesEtale U` generated by identity-degree stage
étale covers. -/
def spacesEtaleTotalTopology : GrothendieckTopology (SpacesEtale U) :=
  (spacesEtaleTotalPrecoverage U).toGrothendieck

/-- The total spaces-étale topology is generated by `spacesEtaleTotalPrecoverage U`. -/
theorem spacesEtaleTotalTopology_eq_toGrothendieck :
    spacesEtaleTotalTopology U = (spacesEtaleTotalPrecoverage U).toGrothendieck :=
  rfl

/-- Sheaves of types in universe `u + 1` on the total spaces-étale site admit
sheafification. -/
instance hasSheafify_spacesEtaleTotalTopology :
    HasSheafify (spacesEtaleTotalTopology U) (Type (u + 1)) :=
  sorry

/-- The Case A presenting functor of the spaces-étale augmentation: pull back along
`a.app (op ⦋0⦌)` and include the resulting étale object at degree zero. -/
def augmentationFunctor {X : AlgebraicSpace S}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    spacesEtaleSite X ⥤ SpacesEtale U :=
  spacesEtalePullback (a.app (op ⦋0⦌)) ⋙ SpacesEtale.includeStage (op ⦋0⦌)

/-- On objects, `augmentationFunctor a` is the degree-zero pullback along `a0`. -/
theorem augmentationFunctor_obj {X : AlgebraicSpace S}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) (V : spacesEtaleSite X) :
    (augmentationFunctor U a).obj V =
      SpacesEtale.ofStage (op ⦋0⦌) ((spacesEtalePullback (a.app (op ⦋0⦌))).obj V) :=
  rfl

/-- Base change along `a0` followed by identity-degree inclusion is continuous for
the spaces-étale topologies. -/
instance augmentationFunctor_isContinuous {X : AlgebraicSpace S}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    (augmentationFunctor U a).IsContinuous (spacesEtaleTopology X)
      (spacesEtaleTotalTopology U) :=
  sorry

/-- Opposite of `augmentationFunctor a` admits left Kan extensions of type-valued
presheaves. -/
instance augmentationFunctor_op_hasLeftKanExtension {X : AlgebraicSpace S}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X)
    (P : (spacesEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) :
    (augmentationFunctor U a).op.HasLeftKanExtension P :=
  sorry

/-- Sheaf pullback along `augmentationFunctor a` preserves finite limits. -/
instance augmentationFunctor_sheafPullback_preservesFiniteLimits {X : AlgebraicSpace S}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    PreservesFiniteLimits
      ((augmentationFunctor U a).sheafPullback (Type (u + 1))
        (spacesEtaleTopology X) (spacesEtaleTotalTopology U)) :=
  sorry

/-- The presenting functor of the spaces-étale augmentation is an exact morphism of
sites. -/
instance augmentationFunctor_isExactMorphismOfSites {X : AlgebraicSpace S}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    IsExactMorphismOfSites.{u + 1, u + 1, u + 1, u + 1, u + 1}
      (spacesEtaleTopology X) (spacesEtaleTotalTopology U) (augmentationFunctor U a) :=
  sorry

/-- The right vertical morphism of topoi `a : Sh(U_spaces,étale) ⟶ Sh(X_spaces,étale)`
presented by pullback along `a.app (op ⦋0⦌)`. -/
def spacesEtaleAugmentation {X : AlgebraicSpace S}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    MorphismOfTopoiIn (spacesEtaleTopology X) (spacesEtaleTotalTopology U) :=
  (augmentationFunctor U a).morphismOfTopoiInOfContinuous.{u + 1, u + 1, u + 1, u + 1, u + 1}
    (spacesEtaleTopology X) (spacesEtaleTotalTopology U)

/-- Inverse image of `spacesEtaleAugmentation a` is sheaf pullback along
`augmentationFunctor a`. -/
theorem spacesEtaleAugmentation_inverseImage {X : AlgebraicSpace S}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    (spacesEtaleAugmentation U a)⁻¹ =
      (augmentationFunctor U a).sheafPullback (Type (u + 1))
        (spacesEtaleTopology X) (spacesEtaleTotalTopology U) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
