/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Over.StalkGluing
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePresentation.Over.BaseChange

/-!
# Algebraic-space finite-presentation gluing over a stalk

The 2-fibre product `FP_U ×_{FP_V} FP_{Spec(𝒪_{S,s})}` of algebraic spaces of
finite presentation, together with the comparison from `FP_{U'}` for an open
neighborhood `U'` of `s` containing `U`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open CategoricalPullback
open scoped CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver

/-- The 2-fibre product `FP_U ×_{FP_V} FP_{Spec(𝒪_{S,s})}`, where
`V = (S.fromSpecStalk s) ⁻¹ᵁ U` is the intersection of the stalk scheme with
`U`, and `FP_T` is the category of algebraic spaces of finite presentation over
`T`. -/
abbrev stalkGluingCategory (S : Scheme.{u}) (U : S.Opens) (s : S) :=
  CategoricalPullback
    (baseChange ((S.fromSpecStalk s) ∣_ U))
    (baseChange (stalkOpenIntersection S U s).ι)

/-- The commutative square of finite-presentation base-change functors associated
to an open neighborhood `W` of `s` containing `U`. -/
def neighborhoodGlueSquare (S : Scheme.{u}) (U : S.Opens) (s : S)
    (W : OpenNeighborhoodIndex S U s) :
    CatCommSqOver
      (baseChange ((S.fromSpecStalk s) ∣_ U))
      (baseChange (stalkOpenIntersection S U s).ι)
      (FinitePresentationOver W.toOpen.toScheme) where
  fst := baseChange (S.homOfLE W.unop.2.1)
  snd := baseChange (W.toOpen.fromSpecStalkOfMem s W.unop.2.2)
  iso :=
    (compIso ((S.fromSpecStalk s) ∣_ U) (S.homOfLE W.unop.2.1)).symm ≪≫
      eqToIso
        (congrArg
          (fun g : (stalkOpenIntersection S U s).toScheme ⟶ W.toOpen.toScheme ↦
            baseChange g)
          (AlgebraicGeometry.FinitePresentationOver.OpenNeighborhood.intersection_commutes S U s W)) ≪≫
      compIso (stalkOpenIntersection S U s).ι
        (W.toOpen.fromSpecStalkOfMem s W.unop.2.2)

/-- The functor `FP_{U'} ⥤ FP_U ×_{FP_V} FP_{Spec(𝒪_{S,s})}` given by restriction
to `U` and base change to the stalk scheme. -/
def neighborhoodGlueFunctor (S : Scheme.{u}) (U : S.Opens) (s : S)
    (W : OpenNeighborhoodIndex S U s) :
    FinitePresentationOver W.toOpen.toScheme ⥤ stalkGluingCategory S U s :=
  (neighborhoodGlueSquare S U s W).comparison

/-- Projecting neighborhood glue data to the first factor recovers base change
along `U ⟶ U'`. -/
def neighborhoodGlueFunctor_fst (S : Scheme.{u}) (U : S.Opens) (s : S)
    (W : OpenNeighborhoodIndex S U s) :
    neighborhoodGlueFunctor S U s W ⋙
        π₁ (baseChange ((S.fromSpecStalk s) ∣_ U))
          (baseChange (stalkOpenIntersection S U s).ι) ≅
      baseChange (S.homOfLE W.unop.2.1) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry

/-- Projecting neighborhood glue data to the second factor recovers base change
along `Spec(𝒪_{S,s}) ⟶ U'`. -/
def neighborhoodGlueFunctor_snd (S : Scheme.{u}) (U : S.Opens) (s : S)
    (W : OpenNeighborhoodIndex S U s) :
    neighborhoodGlueFunctor S U s W ⋙
        π₂ (baseChange ((S.fromSpecStalk s) ∣_ U))
          (baseChange (stalkOpenIntersection S U s).ι) ≅
      baseChange (W.toOpen.fromSpecStalkOfMem s W.unop.2.2) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry

/-- Glue data over `W` is isomorphic to glue data of the restriction of the
algebraic space to a smaller neighborhood `W'`. -/
def neighborhoodGlueFunctor_restrict (S : Scheme.{u}) (U : S.Opens) (s : S)
    {W W' : OpenNeighborhoodIndex S U s} (f : W ⟶ W') :
    neighborhoodGlueFunctor S U s W ≅
      baseChange (S.homOfLE (leOfHom f.unop)) ⋙ neighborhoodGlueFunctor S U s W' :=
  NatIso.ofComponents
    (fun X ↦
      CategoricalPullback.mkIso
        (eqToIso
            (congrArg
              (fun g : U.toScheme ⟶ W.toOpen.toScheme ↦ (baseChange g).obj X)
              (S.homOfLE_homOfLE W'.unop.2.1 (leOfHom f.unop)).symm) ≪≫
          (compIso (S.homOfLE W'.unop.2.1) (S.homOfLE (leOfHom f.unop))).app X)
        (eqToIso
            (congrArg
              (fun g : Spec (S.presheaf.stalk s) ⟶ W.toOpen.toScheme ↦
                (baseChange g).obj X)
              (AlgebraicGeometry.FinitePresentationOver.OpenNeighborhood.stalkRestriction_compatibility S U s f).symm) ≪≫
          (compIso (W'.toOpen.fromSpecStalkOfMem s W'.unop.2.2)
              (S.homOfLE (leOfHom f.unop))).app X)
        sorry)
    sorry

end AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver
