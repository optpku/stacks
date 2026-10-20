module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Resize.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Lift

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
open scoped CategoryTheory.Limits.CategoricalPullback

noncomputable section
universe vA uA vB uB vC uC vX uX

namespace CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.Resized

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]
variable {C : Type uC} [Category.{vC} C]
variable {X : Type uX} [Category.{vX} X]
variable {F : A ⥤ C} {G : B ⥤ C}
variable (P : CatCommSqOver F G X)

/-- The specified resized cone; its represented comparison is the universal-property owner. -/
abbrev cone := P.resize.toPseudoPullbackCone.toPseudoCone

variable (W : Cat.{max vA uA vB uB vC uC vX uX, max vA uA vB uB vC uC vX uX})

/-- Cone transformations with a fixed, fully resized apex. -/
abbrev Transformation (P : CatCommSqOver F G X)
    (W : Cat.{max vA uA vB uB vC uC vX uX, max vA uA vB uB vC uC vX uX}) :=
  Pseudofunctor.const (LocallyDiscrete WalkingCospan) W ⟶
    Bicategory.cospan (Functor.asSmall.{max vB uB vX uX} F).toCatHom
      (Functor.asSmall.{max vA uA vX uX} G).toCatHom

/-- Read the two generating naturality isomorphisms as the original heterogeneous square. -/
def squareOfTransformation (η : Transformation P W) : CatCommSqOver F G W where
  fst := (η.app (LocallyDiscrete.mk WalkingCospan.left)).toFunctor ⋙ AsSmall.down
  snd := (η.app (LocallyDiscrete.mk WalkingCospan.right)).toFunctor ⋙ AsSmall.down
  iso := NatIso.ofComponents
    (fun w ↦ AsSmall.down.mapIso
      ((Cat.Hom.toNatIso
        ((η.naturality (Quiver.Hom.toLoc WalkingCospan.Hom.inl)).symm ≪≫
          η.naturality (Quiver.Hom.toLoc WalkingCospan.Hom.inr))).app w))
    (fun _ ↦ sorry)

/-- A modification gives the original pair of natural transformations. -/
def squareMap {η θ : Transformation P W} (Γ : η ⟶ θ) :
    squareOfTransformation P W η ⟶ squareOfTransformation P W θ where
  fst := Functor.whiskerRight (Γ.as.app (LocallyDiscrete.mk WalkingCospan.left)).toNatTrans
    AsSmall.down
  snd := Functor.whiskerRight (Γ.as.app (LocallyDiscrete.mk WalkingCospan.right)).toNatTrans
    AsSmall.down
  w := sorry

/-- Interpret a transformation as its actual original categorical-pullback-valued functor. -/
def diagramFunctor : Transformation P W ⥤ (W ⥤ F ⊡ G) :=
  { obj := squareOfTransformation P W
    map := squareMap P W
    map_id := sorry
    map_comp := sorry } ⋙ (CategoricalPullback.functorEquiv F G W).inverse

/-- Lift cone transformations by the supplied comparison inverse, then resize the apex. -/
def liftFunctor (e : X ≌ F ⊡ G) : Transformation P W ⥤ (W ⟶ (cone P).pt) where
  obj η := ((diagramFunctor P W).obj η ⋙ e.inverse ⋙ AsSmall.up).toCatHom
  map Γ := (Functor.whiskerRight ((diagramFunctor P W).map Γ) (e.inverse ⋙ AsSmall.up)).toCatHom₂
  map_id := sorry
  map_comp := sorry

/-- The supplied comparison equivalence is normalized to the prescribed forward functor. -/
def normalizedEquivalence (e : X ≌ F ⊡ G) (α : e.functor ≅ P.comparison) : X ≌ F ⊡ G :=
  e.changeFunctor α

/-- Reading a represented cone recovers its pullback-valued functor through identity
projection maps; only the normalization of its structural isomorphism changes. -/
def diagramComparisonIso (f : W ⟶ (cone P).pt) :
    f.toFunctor ⋙ AsSmall.down ⋙ P.comparison ≅
      (diagramFunctor P W).obj (((cone P).comparison W).obj f) :=
  NatIso.ofComponents
    (fun _ ↦ CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _) (by sorry))
    (fun _ ↦ sorry)

/-- The represented unit raises the given comparison unit at each original apex object. -/
def liftUnitComponent (e : X ≌ F ⊡ G) (α : e.functor ≅ P.comparison)
    (f : W ⟶ (cone P).pt) :
    f ≅ (liftFunctor P W (normalizedEquivalence P e α)).obj ((cone P).comparison W |>.obj f) :=
  Cat.Hom.isoMk <| NatIso.ofComponents
    (fun w ↦ AsSmall.up.mapIso
      ((normalizedEquivalence P e α).unitIso.app (AsSmall.down.obj (f.toFunctor.obj w)) ≪≫
        (normalizedEquivalence P e α).inverse.mapIso ((diagramComparisonIso P W f).app w)))
    (fun _ ↦ sorry)

/-- The left projection of the lifted comparison counit. -/
def liftCounitLeft (e : X ≌ F ⊡ G) (α : e.functor ≅ P.comparison)
    (η : Transformation P W) :
    (((cone P).comparison W).obj
      ((liftFunctor P W (normalizedEquivalence P e α)).obj η)).app
        (LocallyDiscrete.mk WalkingCospan.left) ≅
      η.app (LocallyDiscrete.mk WalkingCospan.left) :=
  Cat.Hom.isoMk <| NatIso.ofComponents
    (fun w ↦ AsSmall.up.mapIso
      ((CategoricalPullback.π₁ F G).mapIso
        ((normalizedEquivalence P e α).counitIso.app ((diagramFunctor P W).obj η |>.obj w))))
    (fun _ ↦ sorry)

/-- The right projection of the lifted comparison counit. -/
def liftCounitRight (e : X ≌ F ⊡ G) (α : e.functor ≅ P.comparison)
    (η : Transformation P W) :
    (((cone P).comparison W).obj
      ((liftFunctor P W (normalizedEquivalence P e α)).obj η)).app
        (LocallyDiscrete.mk WalkingCospan.right) ≅
      η.app (LocallyDiscrete.mk WalkingCospan.right) :=
  Cat.Hom.isoMk <| NatIso.ofComponents
    (fun w ↦ AsSmall.up.mapIso
      ((CategoricalPullback.π₂ F G).mapIso
        ((normalizedEquivalence P e α).counitIso.app ((diagramFunctor P W).obj η |>.obj w))))
    (fun _ ↦ sorry)

/-- The central component is the left counit followed by the original cone's left generator. -/
def liftCounitCenter (e : X ≌ F ⊡ G) (α : e.functor ≅ P.comparison)
    (η : Transformation P W) :
    (((cone P).comparison W).obj
      ((liftFunctor P W (normalizedEquivalence P e α)).obj η)).app
        (LocallyDiscrete.mk WalkingCospan.one) ≅
      η.app (LocallyDiscrete.mk WalkingCospan.one) :=
  Cat.Hom.isoMk <|
    (Functor.isoWhiskerRight (Cat.Hom.toNatIso (liftCounitLeft P W e α η))
      (Functor.asSmall.{max vB uB vX uX} F)) ≪≫
    (Cat.Hom.toNatIso (η.naturality (Quiver.Hom.toLoc WalkingCospan.Hom.inl))).symm ≪≫
    Functor.leftUnitor _

/-- The counit modification has the two prescribed projection maps and their central composite. -/
def liftCounitComponent (e : X ≌ F ⊡ G) (α : e.functor ≅ P.comparison)
    (η : Transformation P W) :
    ((cone P).comparison W).obj
      ((liftFunctor P W (normalizedEquivalence P e α)).obj η) ≅ η :=
  Pseudofunctor.StrongTrans.isoMk
    (fun j ↦ match j with
      | ⟨none⟩ => liftCounitCenter P W e α η
      | ⟨some WalkingPair.left⟩ => liftCounitLeft P W e α η
      | ⟨some WalkingPair.right⟩ => liftCounitRight P W e α η)
    (fun _ ↦ sorry)

/-- The actual represented equivalence associated with an explicit comparison equivalence. -/
def representedEquivalence (e : X ≌ F ⊡ G) (α : e.functor ≅ P.comparison) :
    (W ⟶ (cone P).pt) ≌ Transformation P W where
  functor := (cone P).comparison W
  inverse := liftFunctor P W (normalizedEquivalence P e α)
  unitIso := NatIso.ofComponents (liftUnitComponent P W e α) (fun _ ↦ sorry)
  counitIso := NatIso.ofComponents (liftCounitComponent P W e α) (fun _ ↦ sorry)
  functor_unitIso_comp := sorry

/-- Explicit comparison equivalence data supply every represented bilimit witness. -/
theorem isBilimitOfComparisonEquivalence (e : X ≌ F ⊡ G) (α : e.functor ≅ P.comparison) :
    IsBilimit P where
  comparison_isEquivalence W := (representedEquivalence P W e α).isEquivalence_functor

/-- Raise an original pullback-valued diagram to the normalized walking-cospan cone. -/
def squareOfDiagram (P : CatCommSqOver F G X)
    (W : Cat.{max vA uA vB uB vC uC vX uX, max vA uA vB uB vC uC vX uX})
    (R : W ⥤ F ⊡ G) :
    CatCommSqOver (Functor.asSmall.{max vB uB vX uX} F)
      (Functor.asSmall.{max vA uA vX uX} G) W where
  fst := R ⋙ CategoricalPullback.π₁ F G ⋙ AsSmall.up
  snd := R ⋙ CategoricalPullback.π₂ F G ⋙ AsSmall.up
  iso := NatIso.ofComponents (fun w ↦ AsSmall.up.mapIso (R.obj w).iso) (fun _ ↦ sorry)

/-- The explicit transformation associated with the raised diagram. -/
def transformationOfDiagram (R : W ⥤ F ⊡ G) : Transformation P W :=
  (squareOfDiagram P W R).toPseudoPullbackCone.toPseudoCone.π

/-- The represented equivalence selected from the caller's actual bilimit witness. -/
def equivalenceOfWitness (h : IsBilimit P) :
    (W ⟶ (cone P).pt) ≌ Transformation P W := by
  letI : (cone P).IsBilimit := h
  exact ((cone P).comparison W).asEquivalence

/-- The common-universe test category for the original explicit pullback. -/
abbrev pullbackTest (P : CatCommSqOver F G X) :=
  Cat.of (AsSmall.{max vA uA vB uB vC uC vX uX} (F ⊡ G))

/-- Lift the original explicit pullback diagram using the represented universal witness. -/
def pullbackLift (h : IsBilimit P) : pullbackTest (P := P) ⟶ (cone P).pt :=
  (equivalenceOfWitness P (pullbackTest (P := P)) h).inverse.obj
    (transformationOfDiagram P (pullbackTest (P := P)) AsSmall.down)

/-- The original comparison inverse uses the actual lifted map and the native universe
up/down functors, with no comparison-equivalence factory. -/
def inverseOfWitness (h : IsBilimit P) : F ⊡ G ⥤ X :=
  AsSmall.up ⋙ (pullbackLift P h).toFunctor ⋙ AsSmall.down

/-- Read a specified isomorphism of modifications at a diagram vertex. -/
def modificationComponentIso {η θ : Transformation P W} (ε : η ≅ θ)
    (j : LocallyDiscrete WalkingCospan) : η.app j ≅ θ.app j where
  hom := ε.hom.as.app j
  inv := ε.inv.as.app j
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The actual left projection of the counit for the lifted original pullback. -/
def witnessCounitLeft (h : IsBilimit P) (x : F ⊡ G) :
    P.fst.obj ((inverseOfWitness P h).obj x) ≅ x.fst :=
  AsSmall.down.mapIso
    ((Cat.Hom.toNatIso
      (modificationComponentIso P (pullbackTest (P := P))
        ((equivalenceOfWitness P (pullbackTest (P := P)) h).counitIso.app
          (transformationOfDiagram P (pullbackTest (P := P)) AsSmall.down))
        (LocallyDiscrete.mk WalkingCospan.left))).app (show pullbackTest (P := P) from ⟨x⟩))

/-- The actual right projection of the counit for the lifted original pullback. -/
def witnessCounitRight (h : IsBilimit P) (x : F ⊡ G) :
    P.snd.obj ((inverseOfWitness P h).obj x) ≅ x.snd :=
  AsSmall.down.mapIso
    ((Cat.Hom.toNatIso
      (modificationComponentIso P (pullbackTest (P := P))
        ((equivalenceOfWitness P (pullbackTest (P := P)) h).counitIso.app
          (transformationOfDiagram P (pullbackTest (P := P)) AsSmall.down))
        (LocallyDiscrete.mk WalkingCospan.right))).app (show pullbackTest (P := P) from ⟨x⟩))

/-- The comparison counit is the explicit pair of projected universal counit maps. -/
def counitOfWitness (h : IsBilimit P) :
    inverseOfWitness P h ⋙ P.comparison ≅ 𝟭 (F ⊡ G) :=
  NatIso.ofComponents
    (fun x ↦ CategoricalPullback.mkIso
      (witnessCounitLeft P h x) (witnessCounitRight P h x) (by sorry))
    (fun _ ↦ sorry)

/-- The common-universe test category for the original square apex. -/
abbrev apexTest (P : CatCommSqOver F G X) := Cat.of (AsSmall.{max vA uA vB uB vC uC vX uX} X)

/-- The apex endofunctor whose comparison is identified by the projected counit. -/
def recoveryMap (h : IsBilimit P) : apexTest (P := P) ⟶ (cone P).pt :=
  (AsSmall.down ⋙ P.comparison ⋙ inverseOfWitness P h ⋙ AsSmall.up).toCatHom

/-- The comparison of the recovered apex map has an explicit isomorphism to the original
comparison, whose two legs are the counit projections. -/
def recoveryComparisonIso (h : IsBilimit P) :
    ((cone P).comparison (apexTest (P := P))).obj (recoveryMap P h) ≅
      ((cone P).comparison (apexTest (P := P))).obj (𝟙 (cone P).pt) :=
  Pseudofunctor.StrongTrans.isoMk
    (fun j ↦ match j with
      | ⟨none⟩ => Cat.Hom.isoMk <| NatIso.ofComponents
          (fun x ↦ AsSmall.up.mapIso
            (F.mapIso (witnessCounitLeft P h (P.comparison.obj (AsSmall.down.obj x)))))
          (fun _ ↦ sorry)
      | ⟨some WalkingPair.left⟩ => Cat.Hom.isoMk <| NatIso.ofComponents
          (fun x ↦ AsSmall.up.mapIso
            (witnessCounitLeft P h (P.comparison.obj (AsSmall.down.obj x))))
          (fun _ ↦ sorry)
      | ⟨some WalkingPair.right⟩ => Cat.Hom.isoMk <| NatIso.ofComponents
          (fun x ↦ AsSmall.up.mapIso
            (witnessCounitRight P h (P.comparison.obj (AsSmall.down.obj x))))
          (fun _ ↦ sorry))
    (fun _ ↦ sorry)

/-- Full faithfulness of the actual represented equivalence recovers the apex unit. -/
def recoveredUnit (h : IsBilimit P) :
    𝟙 (cone P).pt ≅ recoveryMap P h :=
  (equivalenceOfWitness P (apexTest (P := P)) h).fullyFaithfulFunctor.preimageIso
    (recoveryComparisonIso P h).symm

/-- Descend the recovered apex unit through the native universe wrappers. -/
def unitOfWitness (h : IsBilimit P) :
    𝟭 X ≅ P.comparison ⋙ inverseOfWitness P h :=
  NatIso.ofComponents
    (fun x ↦ AsSmall.down.mapIso
      ((Cat.Hom.toNatIso (recoveredUnit P h)).app (AsSmall.up.obj x)))
    (fun _ ↦ sorry)

/-- The original comparison equivalence with its inverse and both comparisons extracted
from the caller's actual universal witness. -/
def comparisonEquivalenceOfIsBilimit (h : IsBilimit P) : X ≌ F ⊡ G where
  functor := P.comparison
  inverse := inverseOfWitness P h
  unitIso := unitOfWitness P h
  counitIso := counitOfWitness P h
  functor_unitIso_comp := sorry

end CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.Resized

end
