module

public import ReasLib.CategoryTheory.Sites.Simplicial.MorphismDiagram
public import ReasLib.CategoryTheory.Sites.Topos.Composition

/-!
# Morphisms of covariant simplex diagrams of sites

A natural transformation with exact component functors presents stagewise
morphisms of sites. Its naturality squares induce canonical comparisons
between the inverse images of the corresponding morphisms of topoi.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace CategoryTheory.SimplicialSites

variable {C C' : SimplexCategory ⥤ Cat.{v, u}}
variable (J : ∀ n, Precoverage (C.obj n)) (J' : ∀ n, Precoverage (C'.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J' n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C'.obj m)ᵒᵖ ⥤ Type w),
    ((C'.map φ).toFunctor).op.HasLeftKanExtension P]
variable [instC : IsMorphismDiagram C J] [instC' : IsMorphismDiagram C' J']
include instC instC'

/-- A morphism of covariant simplex diagrams of sites: a natural
transformation `α : C' ⟶ C` whose component functors `(α.app n).toFunctor : C'.obj n ⥤ C.obj n`
are exact morphisms of sites from `(C'.obj n, J' n)` to `(C.obj n, J n)`. Each component
presents a morphism of sites `h_n : C.obj n ⟶ C'.obj n` and a morphism of topoi
`h_n : Sh(C.obj n) ⟶ Sh(C'.obj n)`. -/
class IsMorphism (α : C' ⟶ C) : Prop where
  /-- Each component functor is an exact morphism of sites. -/
  isExact : ∀ (n : SimplexCategory)
    [∀ P : (C'.obj n)ᵒᵖ ⥤ Type w, ((α.app n).toFunctor).op.HasLeftKanExtension P],
    IsExactMorphismOfSites (J' n).toGrothendieck (J n).toGrothendieck (α.app n).toFunctor

/-- A natural transformation of covariant simplex diagrams is a morphism of simplicial sites
iff every component functor is an exact morphism of sites. -/
theorem IsMorphism.iff (α : C' ⟶ C)
    [∀ n (P : (C'.obj n)ᵒᵖ ⥤ Type w), ((α.app n).toFunctor).op.HasLeftKanExtension P] :
    IsMorphism J J' α ↔
      ∀ (n : SimplexCategory),
        IsExactMorphismOfSites (J' n).toGrothendieck (J n).toGrothendieck (α.app n).toFunctor :=
  sorry

/-- The identity transformation of a morphism diagram is a morphism of simplicial sites. -/
instance IsMorphism.id : IsMorphism J J (𝟙 C) :=
  sorry

variable (α : C' ⟶ C)
variable [∀ n (P : (C'.obj n)ᵒᵖ ⥤ Type w), ((α.app n).toFunctor).op.HasLeftKanExtension P]
variable [hα : IsMorphism J J' α]
include hα

/-- Every component of a morphism of simplicial sites is an exact morphism of sites. -/
instance IsMorphism.instIsExact (n : SimplexCategory) :
    IsExactMorphismOfSites (J' n).toGrothendieck (J n).toGrothendieck (α.app n).toFunctor :=
  hα.isExact n

/-- Every component functor is continuous for the generated stage topologies. -/
instance IsMorphism.instIsContinuous (n : SimplexCategory) :
    ((α.app n).toFunctor).IsContinuous (J' n).toGrothendieck (J n).toGrothendieck :=
  inferInstance

/-- The sheaf inverse image along each component preserves finite limits. -/
instance IsMorphism.instSheafPullbackPreservesFiniteLimits (n : SimplexCategory) :
    PreservesFiniteLimits
      ((α.app n).toFunctor.sheafPullback (Type w) (J' n).toGrothendieck (J n).toGrothendieck) :=
  (hα.isExact n).preservesFiniteLimits_sheafPullback

/-- Naturality of `α` as functors of stage categories: `u'_φ ⋙ v_n = v_m ⋙ u_φ`. -/
theorem IsMorphism.naturality_toFunctor {m n : SimplexCategory} (φ : m ⟶ n) :
    (C'.map φ).toFunctor ⋙ (α.app n).toFunctor =
      (α.app m).toFunctor ⋙ (C.map φ).toFunctor :=
  sorry

/-- The morphism of topoi `h_n : Sh(C.obj n) ⟶ Sh(C'.obj n)` presented by the component
`(α.app n).toFunctor : C'.obj n ⥤ C.obj n`. -/
def IsMorphism.topos (n : SimplexCategory) :
    MorphismOfTopoiIn (J' n).toGrothendieck (J n).toGrothendieck :=
  (α.app n).toFunctor.morphismOfTopoiInOfContinuous (J' n).toGrothendieck (J n).toGrothendieck

/-- Inverse image of `IsMorphism.topos` is sheaf pullback along the component functor. -/
theorem IsMorphism.topos_inverseImage (n : SimplexCategory) :
    (IsMorphism.topos J J' α n).inverseImage =
      (α.app n).toFunctor.sheafPullback (Type w) (J' n).toGrothendieck (J n).toGrothendieck :=
  sorry

/-- Inverse images of `f'_φ ∘ h_n` and `h_m ∘ f_φ` are canonically isomorphic, as morphisms of
topoi, by the continuous-square comparison. -/
def IsMorphism.inverseImage_naturality {m n : SimplexCategory} (φ : m ⟶ n) :
    (toposMap C' J' φ).inverseImage ⋙ (IsMorphism.topos J J' α n).inverseImage ≅
      (IsMorphism.topos J J' α m).inverseImage ⋙ (toposMap C J φ).inverseImage :=
  Functor.ContinuousSquare.pullbackIso (Type w)
    (congrArg Cat.Hom.toFunctor (α.naturality φ)).symm

end CategoryTheory.SimplicialSites

