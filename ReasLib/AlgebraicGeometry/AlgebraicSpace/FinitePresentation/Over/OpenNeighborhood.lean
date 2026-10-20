module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.Grothendieck
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePresentation.Over.BaseChange.Identity
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePresentation.Over.NeighborhoodGluing

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
              (S.homOfLE_rfl W.toOpen)) ≪≫
          baseChange_id W.toOpen.toScheme))
    (fun {W₀ W₁ W₂} (f : W₀ ⟶ W₁) (g : W₁ ⟶ W₂) ↦
      Cat.Hom.isoMk
        (eqToIso
            (congrArg
              (fun φ : W₂.toOpen.toScheme ⟶ W₀.toOpen.toScheme ↦ baseChange φ)
              (S.homOfLE_homOfLE (leOfHom g.unop) (leOfHom f.unop)).symm) ≪≫
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

/-- For a retrocompact open of a scheme and a point outside it, restriction
induces an equivalence from the colimit of finite-presentation algebraic spaces
over open neighborhoods containing the open and the point to their gluing
category over the open and the local spectrum. -/
theorem comparison_isEquivalence (S : Scheme.{u}) (U : S.Opens)
    [AlgebraicGeometry.QuasiCompact U.ι] (s : S) (hsU : s ∉ (U : Set S)) :
    (OpenNeighborhood.comparison S U s).IsEquivalence :=
  sorry

/-- The neighborhood comparison is an equivalence when nonmembership of the
point in the retrocompact open is supplied by a `Fact` instance. -/
instance comparison_isEquivalence_of_fact (S : Scheme.{u}) (U : S.Opens)
    [AlgebraicGeometry.QuasiCompact U.ι] (s : S) [Fact (s ∉ (U : Set S))] :
    (OpenNeighborhood.comparison S U s).IsEquivalence :=
  comparison_isEquivalence S U s Fact.out

end AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver
