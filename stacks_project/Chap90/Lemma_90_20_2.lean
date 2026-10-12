/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.IsomorphismClasses
public import stacks_project.Chap90.Definition_90_8_1_Smooth
public import stacks_project.Chap90.Definition_90_16_8
public import stacks_project.Chap90.Lemma_90_19_10_LinearMap
public import stacks_project.Chap90.Lemma_90_20_2_Comparison
public import stacks_project.Chap90.Remark_90_19_4_InfinitesimalAut

/-!
# Smoothness of the induced map of 2-fibre products

If `H1 ⟶ G`, `H2 ⟶ G`, and `G ⟶ F` are morphisms of categories cofibered in
groupoids, `F` and `G` are deformation categories, `TG ⟶ TF` is injective, and
`Inf(G) ⟶ Inf(F)` is surjective, then `H1 ×_G H2 ⟶ H1 ×_F H2` is smooth.
-/

@[expose] public section

noncomputable section

open CategoryTheory ArtinianLocalAlgCat Functor BasedCategory
open CofiberedCategoryOver.Groupoids
open scoped Bicategory BasedFunctor
open Fiber
open Functor.Chosen

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {H1 H2 G F :
    CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k)}

namespace CategoryTheory.Functor

/-- The `ofFunctor` presentation of a predeformation category is a predeformation category. -/
instance instIsPredeformationCategory_ofFunctor
    {E : Type v} [Category.{w} E] (r : E ⥤ ArtinianLocalAlgCat Λ k)
    [IsPredeformationCategory r] :
    IsPredeformationCategory (BasedCategory.ofFunctor r).p :=
  inferInstanceAs (IsPredeformationCategory r)

/-- A deformation category satisfies the Rim-Schlessinger condition. -/
instance instHasRimSchlessinger_of_isDeformationCategory
    {E : Type v} [Category.{w} E] (r : E ⥤ ArtinianLocalAlgCat Λ k)
    [h : IsDeformationCategory r] : HasRimSchlessinger r :=
  h.hasRimSchlessinger

end CategoryTheory.Functor

namespace CategoryTheory.CofiberedCategoryOver.Groupoids

/-- Convert a morphism of categories cofibered in groupoids into a based functor between the
`ofFunctor` presentations of the projections. -/
def toOfFunctor {X Y :
    CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k)}
    (φ : X ⟶ Y) :
    BasedCategory.ofFunctor X.p ⥤ᵇ BasedCategory.ofFunctor Y.p :=
  BasedFunctor.ofFunctor (toBasedFunctor φ).toFunctor (toBasedFunctor φ).w

/-- `toOfFunctor` is the `ofFunctor` packaging of the underlying total-category functor. -/
theorem toOfFunctor_toFunctor {X Y :
    CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k)}
    (φ : X ⟶ Y) :
    (toOfFunctor φ).toFunctor = (toBasedFunctor φ).toFunctor := sorry

end CategoryTheory.CofiberedCategoryOver.Groupoids

namespace CategoryTheory.BasedFunctor

/-- The image of a dual-number pushforward under an `ofFunctor` based functor is strongly
cocartesian over `residueToDualNumber` as a morphism of the target projection. -/
instance instIsStronglyCocartesian_mapPushforward [IsDeformationCategory G.p]
    [IsDeformationCategory F.p]
    (φ : BasedCategory.ofFunctor G.p ⥤ᵇ BasedCategory.ofFunctor F.p)
    {x0 : G.p.Fiber (residue Λ k)} {x0' : G.p.Fiber (dualNumber Λ k)}
    (ψ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [G.p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ] :
    (BasedCategory.ofFunctor F.p).p.IsStronglyCocartesian (residueToDualNumber Λ k)
      (mapPushforward φ ψ) := sorry

/-- The differential `TG ⟶ TF` of a morphism of predeformation categories, as the map on
isomorphism classes of dual-number fibres. -/
def differential [IsPredeformationCategory G.p] [IsPredeformationCategory F.p]
    (φ : BasedCategory.ofFunctor G.p ⥤ᵇ BasedCategory.ofFunctor F.p) :
    isomorphismClasses.obj (Cat.of (G.p.Fiber (dualNumber Λ k))) →
      isomorphismClasses.obj (Cat.of (F.p.Fiber (dualNumber Λ k))) :=
  (φ.fiberFunctor (dualNumber Λ k)).isoClassesMap

/-- The differential sends the isomorphism class of a fibre object to the class of its image. -/
theorem differential_mk [IsPredeformationCategory G.p] [IsPredeformationCategory F.p]
    (φ : BasedCategory.ofFunctor G.p ⥤ᵇ BasedCategory.ofFunctor F.p)
    (x : G.p.Fiber (dualNumber Λ k)) :
    differential φ (Quotient.mk'' x) =
      Quotient.mk'' ((φ.fiberFunctor (dualNumber Λ k)).obj x) := sorry

/-- The unpointed map on infinitesimal automorphisms induced by a morphism of deformation
categories, obtained by conjugating `infAutLinearMap` along `infinitesimalAutomorphismsEquivAt`
at the chosen dual-number pushforwards. -/
def mapInfinitesimalAutomorphisms [IsDeformationCategory G.p]
    [IsDeformationCategory F.p] (φ : BasedCategory.ofFunctor G.p ⥤ᵇ BasedCategory.ofFunctor F.p) :
    infinitesimalAutomorphisms G.p → infinitesimalAutomorphisms F.p :=
  fun α ↦
    let x0 := chosenResidueFiberObj G.p
    let x0' := pushforwardObj G.p (residueToDualNumber Λ k) x0
    let ψ := chosenDualNumberHom G.p x0
    (infinitesimalAutomorphismsEquivAt (BasedCategory.ofFunctor F.p).p
          ((φ.fiberFunctor (residue Λ k)).obj x0)
          ((φ.fiberFunctor (dualNumber Λ k)).obj x0') (mapPushforward φ ψ)).symm
      (infAutLinearMap φ ψ (infinitesimalAutomorphismsEquivAt G.p x0 x0' ψ α))

/-- `mapInfinitesimalAutomorphisms` conjugates `infAutLinearMap` along the chosen
`infinitesimalAutomorphismsEquivAt` identifications. -/
theorem mapInfinitesimalAutomorphisms_apply [IsDeformationCategory G.p]
    [IsDeformationCategory F.p] (φ : BasedCategory.ofFunctor G.p ⥤ᵇ BasedCategory.ofFunctor F.p)
    (α : infinitesimalAutomorphisms G.p) :
    mapInfinitesimalAutomorphisms φ α =
      let x0 := chosenResidueFiberObj G.p
      let x0' := pushforwardObj G.p (residueToDualNumber Λ k) x0
      let ψ := chosenDualNumberHom G.p x0
      (infinitesimalAutomorphismsEquivAt (BasedCategory.ofFunctor F.p).p
            ((φ.fiberFunctor (residue Λ k)).obj x0)
            ((φ.fiberFunctor (dualNumber Λ k)).obj x0') (mapPushforward φ ψ)).symm
        (infAutLinearMap φ ψ (infinitesimalAutomorphismsEquivAt G.p x0 x0' ψ α)) := sorry

/-- Lemma 90.20.2: if `p1 : H1 ⟶ G`, `p2 : H2 ⟶ G`, and `q : G ⟶ F` are morphisms of
categories cofibered in groupoids over `ArtinianLocalAlgCat Λ k`, `F` and `G` are
deformation categories, `differential (toOfFunctor q) : TG ⟶ TF` is injective, and
`mapInfinitesimalAutomorphisms (toOfFunctor q) : Inf(G) ⟶ Inf(F)` is surjective, then
the induced map `TwoFibreProduct.apex p1 p2 ⟶ TwoFibreProduct.apex (p1 ≫ q) (p2 ≫ q)`
is smooth. -/
@[stacks 0DYN]
theorem isSmooth_mapPostcompose (p1 : H1 ⟶ G) (p2 : H2 ⟶ G) (q : G ⟶ F)
    [IsDeformationCategory F.p] [IsDeformationCategory G.p]
    (hT : Function.Injective (differential (toOfFunctor q)))
    (hInf : Function.Surjective (mapInfinitesimalAutomorphisms (toOfFunctor q))) :
    IsSmooth (toBasedFunctor (TwoFibreProduct.mapPostcompose p1 p2 q)) := sorry

end CategoryTheory.BasedFunctor
