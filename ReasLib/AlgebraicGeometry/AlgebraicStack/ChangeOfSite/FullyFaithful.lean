/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ChangeOfSite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfSite.FullyFaithful
public import ReasLib.CategoryTheory.Bicategory.LocalProperties
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Pushforward.Hom
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Pushforward.Pullback
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Postcomposition

/-!
# Fully faithful enlargement of the site of algebraic stacks
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Bicategory

noncomputable section

universe u v w

namespace AlgebraicGeometry.ChosenBigFppfSite

variable (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
variable [hSheafify : HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [hSheafPullbacks : HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]

/-- The property selecting algebraic stacks in groupoids on a chosen slice site. -/
def algebraicStackProperty :
    ObjectProperty (StackOver.{_, _, max u v w, max u v w} (𝒮.bigTopology S)) :=
  fun X ↦ IsStack.InGroupoids (𝒮.bigTopology S) X.p ∧ IsAlgebraicStack 𝒮 S X

/-- The full bicategory of algebraic stacks in groupoids over a chosen base,
with total objects and total morphisms in a common ambient universe. -/
abbrev AlgebraicStacks := (algebraicStackProperty.{u, v, w} 𝒮 S).FullSubbicategory

namespace AlgebraicStacks

/-- Package an algebraic stack in groupoids as an object of the full bicategory. -/
def of (X : StackOver.{_, _, max u v w, max u v w} (𝒮.bigTopology S))
    (hX : IsStack.InGroupoids (𝒮.bigTopology S) X.p)
    (hAlg : IsAlgebraicStack 𝒮 S X) : AlgebraicStacks.{u, v, w} 𝒮 S :=
  ObjectProperty.FullSubbicategory.mk _ X ⟨hX, hAlg⟩

/-- The underlying stack on the chosen slice site. -/
abbrev toStackOver (X : AlgebraicStacks.{u, v, w} 𝒮 S) :
    StackOver.{_, _, max u v w, max u v w} (𝒮.bigTopology S) := X.1

/-- The canonical inclusion of algebraic stacks into all stacks on the slice site. -/
abbrev forget : StrictPseudofunctor (AlgebraicStacks.{u, v, w} 𝒮 S)
    (StackOver.{_, _, max u v w, max u v w} (𝒮.bigTopology S)) :=
  ObjectProperty.FullSubbicategory.ι (algebraicStackProperty 𝒮 S)

/-- Packaging an algebraic stack and then forgetting returns the original stack. -/
@[simp]
theorem of_toStackOver
    (X : StackOver.{_, _, max u v w, max u v w} (𝒮.bigTopology S))
    (hX : IsStack.InGroupoids (𝒮.bigTopology S) X.p)
    (hAlg : IsAlgebraicStack 𝒮 S X) :
    toStackOver 𝒮 S (of 𝒮 S X hX hAlg) = X := rfl

/-- The inclusion sends an algebraic stack to its underlying stack. -/
@[simp]
theorem forget_obj (X : AlgebraicStacks.{u, v, w} 𝒮 S) :
    (forget 𝒮 S).obj X = toStackOver 𝒮 S X := rfl

/-- Forget the algebraicity and stack conditions on a morphism category,
retaining its cartesian functors and vertical natural transformations. -/
def toCartesianFunctor (X Y : AlgebraicStacks.{u, v, w} 𝒮 S) :
    (X ⟶ Y) ⥤ CartesianBasedFunctor (toStackOver 𝒮 S X).p (toStackOver 𝒮 S Y).p :=
  (forget 𝒮 S).toPseudofunctor.mapFunctor X Y ⋙
    (StackOver.forget (𝒮.bigTopology S)).toPseudofunctor.mapFunctor
      (toStackOver 𝒮 S X) (toStackOver 𝒮 S Y) ⋙
    FiberedCategoryOver.CartesianHom.fromHom
      (toStackOver 𝒮 S X).toFiberedCategoryOver
      (toStackOver 𝒮 S Y).toFiberedCategoryOver

end AlgebraicStacks

variable (𝒯 : ChosenBigFppfSite.{u, v})
variable (inclusion : 𝒮.carrier ⥤ 𝒯.carrier)
variable [hSheafify' : HasWeakSheafify (𝒯.bigTopology (inclusion.obj S)) (Type (max u v))]
variable [hSheafPullbacks' : HasPullbacks (Sheaf (𝒯.bigTopology (inclusion.obj S)) (Type (max u v)))]
variable [hContinuous : (Over.post (X := S) inclusion).IsContinuous
  (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S))]
variable [hKan : ∀ P : (Over S)ᵒᵖ ⥤ Type (max u v),
  (Over.post (X := S) inclusion).op.HasLeftKanExtension P]
variable [hPullbacks : HasPullbacks (Over S)] [hEqualizers : HasEqualizers (Over S)]
variable [hPostPullbacks : PreservesLimitsOfShape WalkingCospan (Over.post (X := S) inclusion)]
variable [hPostEqualizers : PreservesLimitsOfShape WalkingParallelPair
  (Over.post (X := S) inclusion)]

/-- A pseudofunctor is inverse image if its objects are stackifications of
the actual pushforwards and its Hom actions agree naturally with the forward
pushforward-pullback comparisons. -/
def AlgebraicStacks.IsInverseImage
    (F : Pseudofunctor (AlgebraicStacks.{u, v, w} 𝒮 S)
      (AlgebraicStacks.{u, v, w} 𝒯 (inclusion.obj S))) : Prop :=
  ∃ (h : ∀ X : AlgebraicStacks.{u, v, w} 𝒮 S,
      FiberedCategoryOver.Pushforward.ProjectionChoice (Over.post (X := S) inclusion)
        (AlgebraicStacks.toStackOver 𝒮 S X).toFiberedCategoryOver)
    (c : ∀ X : AlgebraicStacks.{u, v, w} 𝒮 S,
      CartesianBasedFunctor
        (FiberedCategoryOver.pushforward (Over.post (X := S) inclusion)
          (AlgebraicStacks.toStackOver 𝒮 S X).toFiberedCategoryOver (h X)).p
        (AlgebraicStacks.toStackOver 𝒯 (inclusion.obj S) (F.obj X)).p),
    (∀ X, CartesianBasedFunctor.IsStackification
      (𝒯.bigTopology (inclusion.obj S)) (c X)) ∧
    ∀ X Y, Nonempty
      (F.mapFunctor X Y ⋙
          AlgebraicStacks.toCartesianFunctor 𝒯 (inclusion.obj S) (F.obj X) (F.obj Y) ⋙
          CartesianBasedFunctor.PushforwardHom.functor (c X)
            (AlgebraicStacks.toStackOver 𝒯 (inclusion.obj S) (F.obj Y)).toFiberedCategoryOver ≅
        AlgebraicStacks.toCartesianFunctor 𝒮 S X Y ⋙
          CartesianBasedFunctor.postcomp (AlgebraicStacks.toStackOver 𝒮 S X).p
            (CartesianBasedFunctor.PushforwardHom.pullbackComparison (c Y)))

/-- An algebraic stack on the larger site has a smaller-site presentation
when it admits a smooth algebraic-space groupoid presentation whose object
and arrow sheaves are pullbacks of smaller-site algebraic spaces. -/
def HasSmallSitePresentation (X' : AlgebraicStacks.{u, v, w} 𝒯 (inclusion.obj S)) : Prop :=
  ∃ (B : Sheaf (𝒯.bigTopology (inclusion.obj S)) (Type (max u v)))
    (G : SheafGroupoid (𝒯.bigTopology (inclusion.obj S)) B),
    IsAlgebraicSpace B ∧ IsAlgebraicSpace G.U.left ∧ IsAlgebraicSpace G.R.left ∧
    IsSmooth 𝒯 (inclusion.obj S) G.s.left ∧ IsSmooth 𝒯 (inclusion.obj S) G.t.left ∧
    (∃ E : CartesianBasedFunctor G.quotientStack.p
        (AlgebraicStacks.toStackOver 𝒯 (inclusion.obj S) X').p,
      E.toBasedFunctor.IsEquivalence) ∧
    ∃ U R : Spaces 𝒮 S,
      Nonempty (((Over.post (X := S) inclusion).sheafPullback (Type (max u v))
        (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S))).obj U.obj ≅ G.U.left) ∧
      Nonempty (((Over.post (X := S) inclusion).sheafPullback (Type (max u v))
        (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S))).obj R.obj ≅ G.R.left)

omit hPullbacks hEqualizers hPostPullbacks hPostEqualizers in
/-- The smaller-site presentation predicate is exactly the existence of a
smooth quotient presentation with independently descending object and arrow spaces. -/
theorem hasSmallSitePresentation_iff
    (X' : AlgebraicStacks.{u, v, w} 𝒯 (inclusion.obj S)) :
    HasSmallSitePresentation 𝒮 S 𝒯 inclusion X' ↔
      ∃ (B : Sheaf (𝒯.bigTopology (inclusion.obj S)) (Type (max u v)))
        (G : SheafGroupoid (𝒯.bigTopology (inclusion.obj S)) B),
        IsAlgebraicSpace B ∧ IsAlgebraicSpace G.U.left ∧ IsAlgebraicSpace G.R.left ∧
        IsSmooth 𝒯 (inclusion.obj S) G.s.left ∧ IsSmooth 𝒯 (inclusion.obj S) G.t.left ∧
        (∃ E : CartesianBasedFunctor G.quotientStack.p
            (AlgebraicStacks.toStackOver 𝒯 (inclusion.obj S) X').p,
          E.toBasedFunctor.IsEquivalence) ∧
        ∃ U R : Spaces 𝒮 S,
          Nonempty (((Over.post (X := S) inclusion).sheafPullback (Type (max u v))
            (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S))).obj U.obj ≅ G.U.left) ∧
          Nonempty (((Over.post (X := S) inclusion).sheafPullback (Type (max u v))
            (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S))).obj R.obj ≅ G.R.left) :=
  Iff.rfl

variable (e : inclusion ⋙ 𝒯.toScheme ≅ 𝒮.toScheme)
variable [hFull : inclusion.Full] [hFaithful : inclusion.Faithful]
variable [hSubcanonical : (𝒮.bigTopology S).Subcanonical]
variable [hLimits : PreservesLimitsOfShape WalkingCospan inclusion]
variable [hCocontinuous : (Over.post (X := S) inclusion).IsCocontinuous
  (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S))]
variable [hFiniteLimits : PreservesFiniteLimits
  ((Over.post (X := S) inclusion).sheafPullback (Type (max u v))
    (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S)))]
variable [hSourceFiniteLimits : HasFiniteLimits (Over S)]
variable [hPostFiniteLimits : PreservesFiniteLimits (Over.post (X := S) inclusion)]
variable [hSmall : Small.{w} (Over (inclusion.obj S))]

include e hFull hFaithful hSubcanonical hLimits hContinuous hCocontinuous
  hSheafify hSheafify' hSheafPullbacks hSheafPullbacks' hKan hFiniteLimits hPullbacks hEqualizers hPostPullbacks hPostEqualizers
  hSourceFiniteLimits hPostFiniteLimits hSmall

/-- Inverse image along a scheme-compatible enlargement of chosen big fppf
sites defines a pseudofunctor on algebraic stacks and is an equivalence on
every morphism category. -/
theorem exists_inverseImage_locallyEquivalence :
    ∃ F : Pseudofunctor (AlgebraicStacks.{u, v, w} 𝒮 S)
        (AlgebraicStacks.{u, v, w} 𝒯 (inclusion.obj S)),
      AlgebraicStacks.IsInverseImage 𝒮 S 𝒯 inclusion F ∧ F.IsLocallyEquivalence := sorry

/-- An algebraic stack on the larger site is cartesian equivalent to an
inverse image exactly when it admits a smooth presentation whose object and
arrow spaces are inverse images of smaller-site algebraic spaces. -/
theorem essentiallyInImage_iff (X' : AlgebraicStacks.{u, v, w} 𝒯 (inclusion.obj S)) :
    (∃ (X : AlgebraicStacks.{u, v, w} 𝒮 S)
      (I : StackOver.InverseImage.{_, _, _, _, max u v w, max u v w, max u v w, max u v w}
        (𝒯.bigTopology (inclusion.obj S)) (Over.post (X := S) inclusion)
        (AlgebraicStacks.toStackOver 𝒮 S X)),
      ∃ E : CartesianBasedFunctor I.target.p
        (AlgebraicStacks.toStackOver 𝒯 (inclusion.obj S) X').p,
        E.toBasedFunctor.IsEquivalence) ↔
      HasSmallSitePresentation 𝒮 S 𝒯 inclusion X' := sorry

end AlgebraicGeometry.ChosenBigFppfSite
