module

public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import stacks_project.Chap07.Definition_7_14_1
public import stacks_project.Chap85.Situation_85_3_3_Fiberwise
public import stacks_project.Chap85.Situation_85_3_3_MorphismDiagram

/-!
# Morphisms of simplicial sites

A morphism of simplicial sites in Situation 85.3.3 is a `Cat`-valued natural
transformation whose components are morphisms of sites (case A) or cocontinuous
functors (case B). Naturality of the transformation is the commuting square of
presenting functors; the induced morphisms of topoi then 2-commute by
composition of exact morphisms of sites and of cocontinuous functors.
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

/-- A morphism of simplicial sites in the covariant (case A) presentation: a natural
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
topoi, by the continuous-square comparison for Sites Definition 7.14.5. -/
def IsMorphism.inverseImage_naturality {m n : SimplexCategory} (φ : m ⟶ n) :
    (toposMap C' J' φ).inverseImage ⋙ (IsMorphism.topos J J' α n).inverseImage ≅
      (IsMorphism.topos J J' α m).inverseImage ⋙ (toposMap C J φ).inverseImage :=
  Functor.ContinuousSquare.pullbackIso (Type w)
    (congrArg Cat.Hom.toFunctor (α.naturality φ)).symm

/-- The continuous-square comparison for `IsMorphism.inverseImage_naturality` is invertible. -/
theorem IsMorphism.inverseImage_naturality_hom_comp_inv {m n : SimplexCategory} (φ : m ⟶ n) :
    (IsMorphism.inverseImage_naturality J J' α φ).hom ≫
      (IsMorphism.inverseImage_naturality J J' α φ).inv = 𝟙 _ :=
  sorry

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable {F F' : SimplicialObject Cat.{v, u}}
variable (J : ∀ n, Precoverage (F.obj n)) (J' : ∀ n, Precoverage (F'.obj n))
variable [instF : IsFiberwiseSite F J] [instF' : IsFiberwiseSite F' J']
include instF instF'

/-- A morphism of simplicial sites in the fiberwise (case B) presentation: a natural
transformation `α : F ⟶ F'` whose component functors
`(α.app n).toFunctor : F.obj n ⥤ F'.obj n` are cocontinuous. Each component induces a
morphism of topoi `h_n : Sh(F.obj n) ⟶ Sh(F'.obj n)`. Property `P` is not required of
these components. -/
class IsFiberwiseMorphism (α : F ⟶ F') : Prop where
  /-- Each component functor is cocontinuous for the fiber topologies. -/
  isCocontinuous : ∀ n, ((α.app n).toFunctor).IsCocontinuous
    (J n).toGrothendieck (J' n).toGrothendieck

/-- A natural transformation of fiberwise simplicial sites is a morphism of simplicial sites
iff every component functor is cocontinuous. -/
theorem IsFiberwiseMorphism.iff (α : F ⟶ F') :
    IsFiberwiseMorphism J J' α ↔
      ∀ n, ((α.app n).toFunctor).IsCocontinuous (J n).toGrothendieck (J' n).toGrothendieck :=
  sorry

/-- The identity transformation of a fiberwise simplicial site is a morphism of simplicial
sites. -/
instance IsFiberwiseMorphism.id : IsFiberwiseMorphism J J (𝟙 F) :=
  sorry

variable (α : F ⟶ F')
variable [hα : IsFiberwiseMorphism J J' α]
include hα

/-- Every component of a fiberwise morphism of simplicial sites is cocontinuous. -/
instance IsFiberwiseMorphism.instIsCocontinuous (n : SimplexCategoryᵒᵖ) :
    ((α.app n).toFunctor).IsCocontinuous (J n).toGrothendieck (J' n).toGrothendieck :=
  hα.isCocontinuous n

/-- Naturality of `α` as functors of stage categories: `u_φ ⋙ v_m = v_n ⋙ u'_φ`. -/
theorem IsFiberwiseMorphism.naturality_toFunctor {m n : SimplexCategory} (φ : m ⟶ n) :
    (F.map φ.op).toFunctor ⋙ (α.app (op m)).toFunctor =
      (α.app (op n)).toFunctor ⋙ (F'.map φ.op).toFunctor :=
  sorry

variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasSheafify (J' n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F'.obj (op n))ᵒᵖ ⥤ Type w),
    ((F'.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ n (P : (F.obj n)ᵒᵖ ⥤ Type w),
    ((α.app n).toFunctor).op.HasPointwiseRightKanExtension P]

/-- The morphism of topoi `h_n : Sh(F.obj (op n)) ⟶ Sh(F'.obj (op n))` induced by the
cocontinuous component `(α.app (op n)).toFunctor : F.obj (op n) ⥤ F'.obj (op n)`. -/
def IsFiberwiseMorphism.topos (n : SimplexCategory) :
    MorphismOfTopoiIn (J' (op n)).toGrothendieck (J (op n)).toGrothendieck :=
  (α.app (op n)).toFunctor.morphismOfTopoiInOfCocontinuous
    (J (op n)).toGrothendieck (J' (op n)).toGrothendieck

/-- Inverse image of `IsFiberwiseMorphism.topos` is cocontinuous sheaf pullback along the
component functor. -/
theorem IsFiberwiseMorphism.topos_inverseImage (n : SimplexCategory) :
    (IsFiberwiseMorphism.topos J J' α n).inverseImage =
      (α.app (op n)).toFunctor.sheafPullbackCocontinuous (Type w)
        (J (op n)).toGrothendieck (J' (op n)).toGrothendieck :=
  sorry

variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor ⋙ (α.app (op m)).toFunctor).op.HasPointwiseRightKanExtension P]

/-- Structure maps of the source followed by a fiberwise morphism component are cocontinuous. -/
instance IsFiberwiseMorphism.instIsCocontinuous_comp {m n : SimplexCategory} (φ : m ⟶ n) :
    ((F.map φ.op).toFunctor ⋙ (α.app (op m)).toFunctor).IsCocontinuous
      (J (op n)).toGrothendieck (J' (op m)).toGrothendieck :=
  isCocontinuous_comp (F.map φ.op).toFunctor (α.app (op m)).toFunctor
    (J (op n)).toGrothendieck (J (op m)).toGrothendieck

/-- Inverse images of `f'_φ ∘ h_n` and `h_m ∘ f_φ` are canonically isomorphic, as morphisms of
topoi, by composition of cocontinuous functors in Sites Lemma 7.21.2. -/
def IsFiberwiseMorphism.inverseImage_naturality {m n : SimplexCategory} (φ : m ⟶ n) :
    (toposMap F' J' φ).inverseImage ⋙ (IsFiberwiseMorphism.topos J J' α n).inverseImage ≅
      (IsFiberwiseMorphism.topos J J' α m).inverseImage ⋙ (toposMap F J φ).inverseImage :=
  Adjunction.leftAdjointUniq
    ((Adjunction.comp
        ((F'.map φ.op).toFunctor.sheafPullbackCocontinuousAdjunction
          (J' (op n)).toGrothendieck (J' (op m)).toGrothendieck)
        ((α.app (op n)).toFunctor.sheafPullbackCocontinuousAdjunction
          (J (op n)).toGrothendieck (J' (op n)).toGrothendieck)).ofNatIsoRight
      (Functor.sheafPushforwardCocontinuousComp'
          (J (op n)).toGrothendieck (J' (op n)).toGrothendieck (J' (op m)).toGrothendieck
          (α.app (op n)).toFunctor (F'.map φ.op).toFunctor
          (eqToIso
            (((Cat.Hom.comp_toFunctor (α.app (op n)) (F'.map φ.op)).symm).trans
              ((congrArg Cat.Hom.toFunctor (α.naturality φ.op).symm).trans
                (Cat.Hom.comp_toFunctor (F.map φ.op) (α.app (op m)))))) ≪≫
        (Functor.sheafPushforwardCocontinuousComp'
          (J (op n)).toGrothendieck (J (op m)).toGrothendieck (J' (op m)).toGrothendieck
          (F.map φ.op).toFunctor (α.app (op m)).toFunctor (Iso.refl _)).symm))
    (Adjunction.comp
      ((α.app (op m)).toFunctor.sheafPullbackCocontinuousAdjunction
        (J (op m)).toGrothendieck (J' (op m)).toGrothendieck)
      ((F.map φ.op).toFunctor.sheafPullbackCocontinuousAdjunction
        (J (op n)).toGrothendieck (J (op m)).toGrothendieck))

/-- The comparison `IsFiberwiseMorphism.inverseImage_naturality` is invertible. -/
theorem IsFiberwiseMorphism.inverseImage_naturality_hom_comp_inv
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (IsFiberwiseMorphism.inverseImage_naturality J J' α φ).hom ≫
      (IsFiberwiseMorphism.inverseImage_naturality J J' α φ).inv = 𝟙 _ :=
  sorry

end CategoryTheory.Grothendieck

