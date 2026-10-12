/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.Grothendieck
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Localization.Construction
public import stacks_project.Chap70.Lemma_70_18_3_StalkGluing

/-!
# Neighborhood 2-colimit of algebraic spaces of finite presentation

The 2-colimit of `FP_{U'}` as `U'` runs over open neighborhoods of `s` containing
`U`, modeled by localizing the Grothendieck construction of the base-change
pseudofunctor at fibrewise isomorphisms, and the comparison functor to the
stalk-gluing 2-fibre product.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open CategoricalPullback
open scoped CategoricalPullback
open scoped CategoryTheory.Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver

/-- Base change of functors of points along an identity morphism is isomorphic
to the original functor of points. -/
theorem baseChange_id_functorOfPoints {T : Scheme.{u}} (X : AlgebraicSpace T) :
    (AlgebraicSpace.baseChange (𝟙 T) X).functorOfPoints = X.functorOfPoints :=
  sorry

/-- Base change of algebraic spaces along an identity morphism is isomorphic to
the identity functor. -/
def baseChangeFunctor_id (T : Scheme.{u}) :
    AlgebraicSpace.baseChangeFunctor (𝟙 T) ≅ 𝟭 (AlgebraicSpace T) :=
  NatIso.ofComponents
    (fun X ↦ isoOfFunctorOfPoints (eqToIso (baseChange_id_functorOfPoints X)))
    sorry

/-- Base change along the identity morphism of schemes is isomorphic to the
identity functor on algebraic spaces of finite presentation. -/
def baseChange_id (T : Scheme.{u}) :
    baseChange (𝟙 T) ≅ 𝟭 (FinitePresentationOver T) :=
  NatIso.ofComponents
    (fun X ↦
      { hom := homMk ((baseChangeFunctor_id T).hom.app X.obj)
        inv := homMk ((baseChangeFunctor_id T).inv.app X.obj)
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- The open-inclusion morphism associated to the identity arrow of a
neighborhood index is the identity of the underlying open scheme. -/
theorem homOfLE_unop_id (S : Scheme.{u}) (U : S.Opens) (s : S)
    (W : OpenNeighborhoodIndex S U s) :
    S.homOfLE (leOfHom (𝟙 W).unop) = 𝟙 W.toOpen.toScheme :=
  sorry

/-- The open-inclusion morphism associated to a composite of neighborhood-index
arrows is the composite of the corresponding open inclusions. -/
theorem homOfLE_unop_comp (S : Scheme.{u}) (U : S.Opens) (s : S)
    {W₀ W₁ W₂ : OpenNeighborhoodIndex S U s} (f : W₀ ⟶ W₁) (g : W₁ ⟶ W₂) :
    S.homOfLE (leOfHom (f ≫ g).unop) =
      S.homOfLE (leOfHom g.unop) ≫ S.homOfLE (leOfHom f.unop) :=
  sorry

namespace OpenNeighborhood

/-- The pseudofunctor sending an open neighborhood `U'` of `s` containing `U` to
the category `FP_{U'}` of algebraic spaces of finite presentation over `U'`,
with transition functors given by base change along inclusions. -/
def pseudofunctor (S : Scheme.{u}) (U : S.Opens) (s : S) :
    LocallyDiscrete (OpenNeighborhoodIndex S U s) ⥤ᵖ Cat.{u + 1, u + 1} :=
  LocallyDiscrete.mkPseudofunctor
    (fun W ↦ Cat.of (FinitePresentationOver W.toOpen.toScheme))
    (fun f ↦ (baseChange (S.homOfLE (leOfHom f.unop))).toCatHom)
    (fun W ↦
      Cat.Hom.isoMk
        (eqToIso
            (congrArg
              (fun g : W.toOpen.toScheme ⟶ W.toOpen.toScheme ↦ baseChange g)
              (homOfLE_unop_id S U s W)) ≪≫
          baseChange_id W.toOpen.toScheme))
    (fun {W₀ W₁ W₂} (f : W₀ ⟶ W₁) (g : W₁ ⟶ W₂) ↦
      Cat.Hom.isoMk
        (eqToIso
            (congrArg
              (fun φ : W₂.toOpen.toScheme ⟶ W₀.toOpen.toScheme ↦ baseChange φ)
              (homOfLE_unop_comp S U s f g)) ≪≫
          compIso (S.homOfLE (leOfHom g.unop)) (S.homOfLE (leOfHom f.unop))))
    sorry
    sorry
    sorry

/-- The morphisms in the Grothendieck construction whose component in the target
fibre is an isomorphism. -/
def transitionMorphism (S : Scheme.{u}) (U : S.Opens) (s : S) :
    MorphismProperty (Pseudofunctor.Grothendieck (pseudofunctor S U s)) :=
  fun _ _ f ↦ IsIso f.fiber

/-- The 2-colimit of `FP_{U'}` over open neighborhoods of `s` containing `U`,
modeled by localizing the Grothendieck construction at fibrewise-isomorphism
transition morphisms. -/
abbrev Colimit (S : Scheme.{u}) (U : S.Opens) (s : S) :=
  (transitionMorphism S U s).Localization

/-- The functor from the Grothendieck construction of neighborhood `FP_{U'}` to
the stalk-gluing 2-fibre product, sending an algebraic space over `U'` to its
glue data over `U` and `Spec(𝒪_{S,s})`. -/
def grothendieckToStalkGluing (S : Scheme.{u}) (U : S.Opens) (s : S) :
    Pseudofunctor.Grothendieck (pseudofunctor S U s) ⥤ stalkGluingCategory S U s where
  obj X := (neighborhoodGlueFunctor S U s X.base).obj X.fiber
  map {X Y} f :=
    (neighborhoodGlueFunctor_restrict S U s f.base).hom.app X.fiber ≫
      (neighborhoodGlueFunctor S U s Y.base).map f.fiber
  map_id := sorry
  map_comp := sorry

/-- Fibrewise-isomorphism transition morphisms are inverted by
`grothendieckToStalkGluing`. -/
theorem transitionMorphism_isInvertedBy_grothendieckToStalkGluing
    (S : Scheme.{u}) (U : S.Opens) (s : S) :
    (transitionMorphism S U s).IsInvertedBy (grothendieckToStalkGluing S U s) :=
  sorry

/-- The comparison functor
`colim_{s ∈ U' ⊃ U open} FP_{U'} ⥤ FP_U ×_{FP_V} FP_{Spec(𝒪_{S,s})}`. -/
def comparison (S : Scheme.{u}) (U : S.Opens) (s : S) :
    Colimit S U s ⥤ stalkGluingCategory S U s :=
  Localization.Construction.lift (grothendieckToStalkGluing S U s)
    (transitionMorphism_isInvertedBy_grothendieckToStalkGluing S U s)

/-- After composing with localization, the first projection of the comparison
recovers the first projection of `grothendieckToStalkGluing`. -/
def comparison_fst (S : Scheme.{u}) (U : S.Opens) (s : S) :
    (transitionMorphism S U s).Q ⋙ comparison S U s ⋙
        π₁ (baseChange ((S.fromSpecStalk s) ∣_ U))
          (baseChange (stalkOpenIntersection S U s).ι) ≅
      grothendieckToStalkGluing S U s ⋙
        π₁ (baseChange ((S.fromSpecStalk s) ∣_ U))
          (baseChange (stalkOpenIntersection S U s).ι) :=
  eqToIso
    (congrArg
      (fun F ↦
        F ⋙
          π₁ (baseChange ((S.fromSpecStalk s) ∣_ U))
            (baseChange (stalkOpenIntersection S U s).ι))
      (Localization.Construction.fac (grothendieckToStalkGluing S U s)
        (transitionMorphism_isInvertedBy_grothendieckToStalkGluing S U s)))

/-- After composing with localization, the second projection of the comparison
recovers the second projection of `grothendieckToStalkGluing`. -/
def comparison_snd (S : Scheme.{u}) (U : S.Opens) (s : S) :
    (transitionMorphism S U s).Q ⋙ comparison S U s ⋙
        π₂ (baseChange ((S.fromSpecStalk s) ∣_ U))
          (baseChange (stalkOpenIntersection S U s).ι) ≅
      grothendieckToStalkGluing S U s ⋙
        π₂ (baseChange ((S.fromSpecStalk s) ∣_ U))
          (baseChange (stalkOpenIntersection S U s).ι) :=
  eqToIso
    (congrArg
      (fun F ↦
        F ⋙
          π₂ (baseChange ((S.fromSpecStalk s) ∣_ U))
            (baseChange (stalkOpenIntersection S U s).ι))
      (Localization.Construction.fac (grothendieckToStalkGluing S U s)
        (transitionMorphism_isInvertedBy_grothendieckToStalkGluing S U s)))

end OpenNeighborhood

end AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver
