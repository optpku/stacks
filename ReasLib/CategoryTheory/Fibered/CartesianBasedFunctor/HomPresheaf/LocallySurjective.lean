/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Basic
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.HomPresheaf
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homwise local surjectivity for heterogeneous cartesian functors

This file owns the site-local surjectivity condition on the minimally lifted Hom-presheaf maps of
a universe-polymorphic cartesian based functor. Fixed-universe fibred categories and structured
stack layers expose this property only through their underlying cartesian based functors.
-/

@[expose] public section

universe uC vC uS₁ vS₁ uS₂ vS₂ uS₃ vS₃

namespace CategoryTheory

open scoped CategoryTheory.Bicategory

variable {C : Type uC} [Category.{vC} C]
variable {S₁ : Type uS₁} {S₂ : Type uS₂}
variable [Category.{vS₁} S₁] [Category.{vS₂} S₂]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C} [p₁.IsFibered] [p₂.IsFibered]

namespace CartesianBasedFunctor

namespace Homwise

/-- A heterogeneous cartesian functor is homwise locally surjective when each of its minimally
lifted canonical Hom-presheaf maps is locally surjective on the corresponding slice site. -/
@[stacks 06P2 "heterogeneous homwise local surjectivity"]
def IsLocallySurjective
    (J : GrothendieckTopology C) (F : CartesianBasedFunctor p₁ p₂) : Prop :=
  ∀ {U : C} (x y : p₁.Fiber U),
    Presheaf.IsLocallySurjective (J.over U) (HomPresheaf.Chosen.map F x y)

/-- Homwise local surjectivity is the pointwise local surjectivity of the minimally lifted
canonical Hom-presheaf maps. -/
theorem isLocallySurjective_iff
    (J : GrothendieckTopology C) (F : CartesianBasedFunctor p₁ p₂) :
    IsLocallySurjective J F ↔
      ∀ {U : C} (x y : p₁.Fiber U),
        Presheaf.IsLocallySurjective (J.over U) (HomPresheaf.Chosen.map F x y) := sorry

/-- Every minimally lifted canonical Hom-presheaf map of a homwise locally surjective cartesian
functor is locally surjective. -/
theorem IsLocallySurjective.homPresheafMap
    {J : GrothendieckTopology C} {F : CartesianBasedFunctor p₁ p₂}
    (hF : IsLocallySurjective J F) {U : C} (x y : p₁.Fiber U) :
    Presheaf.IsLocallySurjective (J.over U) (HomPresheaf.Chosen.map F x y) := sorry

/-- The identity cartesian based functor is homwise locally surjective. -/
theorem IsLocallySurjective.id (J : GrothendieckTopology C) :
    IsLocallySurjective J (CartesianBasedFunctor.id p₁) := sorry

/-- Homwise locally surjective heterogeneous cartesian functors are closed under composition. -/
theorem IsLocallySurjective.comp
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C} [p₃.IsFibered]
    {J : GrothendieckTopology C}
    {F : CartesianBasedFunctor p₁ p₂} {G : CartesianBasedFunctor p₂ p₃}
    (hF : IsLocallySurjective J F) (hG : IsLocallySurjective J G) :
    IsLocallySurjective J (F.comp G) := sorry

/-- If a composite is homwise locally surjective, then the right factor is locally surjective on
Hom-presheaves whose endpoints lie in the image of the left factor. -/
theorem IsLocallySurjective.rightOnImage_of_comp
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C} [p₃.IsFibered]
    {J : GrothendieckTopology C}
    {F : CartesianBasedFunctor p₁ p₂} {G : CartesianBasedFunctor p₂ p₃}
    (h : IsLocallySurjective J (F.comp G)) {U : C} (x y : p₁.Fiber U) :
    Presheaf.IsLocallySurjective (J.over U)
      (HomPresheaf.Chosen.map G
        ((F.fiberFunctor U).obj x) ((F.fiberFunctor U).obj y)) := sorry

/-- Homwise local surjectivity is preserved when the topology is enlarged. -/
theorem IsLocallySurjective.of_le
    {J K : GrothendieckTopology C} (hJK : J ≤ K)
    {F : CartesianBasedFunctor p₁ p₂} (hF : IsLocallySurjective J F) :
    IsLocallySurjective K F := sorry

/-- An equivalence over the base is homwise locally surjective. -/
theorem IsLocallySurjective.of_isEquivalence
    (J : GrothendieckTopology C) (F : CartesianBasedFunctor p₁ p₂)
    (hF : F.toBasedFunctor.IsEquivalence) : IsLocallySurjective J F := sorry

/-- Transport homwise local surjectivity along an isomorphism of parallel heterogeneous
cartesian functors. -/
theorem IsLocallySurjective.of_iso
    {J : GrothendieckTopology C} {F G : CartesianBasedFunctor p₁ p₂}
    (e : F ≅ G) (hF : IsLocallySurjective J F) : IsLocallySurjective J G := sorry

/-- Isomorphic parallel heterogeneous cartesian functors are homwise locally surjective
simultaneously. -/
theorem isLocallySurjective_iff_of_iso
    {J : GrothendieckTopology C} {F G : CartesianBasedFunctor p₁ p₂}
    (e : F ≅ G) : IsLocallySurjective J F ↔ IsLocallySurjective J G := sorry

end Homwise

/-- A heterogeneous cartesian functor locally lifts fiber morphisms when its minimally lifted
canonical Hom-presheaf maps are locally surjective. -/
@[stacks 06P2 "heterogeneous local lifting of fiber morphisms"]
abbrev LocallyLifts
    (J : GrothendieckTopology C) (F : CartesianBasedFunctor p₁ p₂) : Prop :=
  Homwise.IsLocallySurjective J F

/-- Local lifting of fiber morphisms is exactly homwise local surjectivity. -/
theorem LocallyLifts.iff_homwise
    (J : GrothendieckTopology C) (F : CartesianBasedFunctor p₁ p₂) :
    LocallyLifts J F ↔ Homwise.IsLocallySurjective J F := sorry

/-- The Hom-presheaf formulation of heterogeneous local lifting is equivalent to lifting every
fiber morphism after passage to a covering sieve. -/
@[stacks 06P2 "coverwise criterion for heterogeneous local lifting"]
theorem LocallyLifts.iff_forall_cover
    {J : GrothendieckTopology C} {F : CartesianBasedFunctor p₁ p₂} :
    LocallyLifts J F ↔
      ∀ {U : C} (x x' : p₁.Fiber U)
        (b : (F.fiberFunctor U).obj x ⟶ (F.fiberFunctor U).obj x'),
        ∃ T : J.Cover U, ∀ I : T.Arrow,
          ∃ a :
            I.f⁎[Functor.Cleavage.ofIsFibered p₁] x ⟶
              I.f⁎[Functor.Cleavage.ofIsFibered p₁] x',
            CommSq
              (((Functor.Cleavage.ofIsFibered p₂).reindex I.f).map b)
              (CartesianBasedFunctor.Reindex.mapIso F
                (Functor.Cleavage.ofIsFibered p₁)
                (Functor.Cleavage.ofIsFibered p₂) I.f x).hom
              (CartesianBasedFunctor.Reindex.mapIso F
                (Functor.Cleavage.ofIsFibered p₁)
                (Functor.Cleavage.ofIsFibered p₂) I.f x').hom
              ((F.fiberFunctor I.Y).map a) := sorry

end CartesianBasedFunctor

end CategoryTheory
