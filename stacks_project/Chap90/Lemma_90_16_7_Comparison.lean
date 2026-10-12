/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import stacks_project.Chap90.«90_10_1_1_Comparison»
public import stacks_project.Chap90.Remarks_90_5_2_IsoClass
public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal

/-!
# Iso-class comparison of a fibre 2-fibre product

A cleavage of `p.op` presents the 2-fibre product of fibres along a cospan
`A1 ⟶ A ⟵ A2` as the categorical pullback of the two pushforward fibre functors.
The induced map on isomorphism classes lands in the type-level fibre product of
the associated isomorphism-class functor.
-/

@[expose] public section

open CategoryTheory Limits CategoricalPullback
open scoped CategoricalPullback

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- The two projected isomorphism classes of an object of the fibre 2-fibre product
agree after applying the fibrewise isomorphism-class functor to the cospan. -/
theorem fiberProductIsoClassComparison_mem
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (χ : p.op.Cleavage) {A A1 A2 : ArtinianLocalAlgCat Λ k}
    (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (x : isomorphismClasses.obj
      (Cat.of ((pushforwardFiberFunctor p χ f1) ⊡ (pushforwardFiberFunctor p χ f2)))) :
    (fiberIsoClassFunctor p).map f1
        ((CategoricalPullback.π₁ (pushforwardFiberFunctor p χ f1)
            (pushforwardFiberFunctor p χ f2)).isoClassesMap x) =
      (fiberIsoClassFunctor p).map f2
        ((CategoricalPullback.π₂ (pushforwardFiberFunctor p χ f1)
            (pushforwardFiberFunctor p χ f2)).isoClassesMap x) :=
  sorry

/-- The induced map from isomorphism classes of
`(pushforwardFiberFunctor p χ f1) ⊡ (pushforwardFiberFunctor p χ f2)` to the
type-level fibre product of fibrewise isomorphism classes. -/
noncomputable def fiberProductIsoClassComparison
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (χ : p.op.Cleavage) {A A1 A2 : ArtinianLocalAlgCat Λ k}
    (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) :
    isomorphismClasses.obj
      (Cat.of ((pushforwardFiberFunctor p χ f1) ⊡ (pushforwardFiberFunctor p χ f2))) →
      Types.PullbackObj ((fiberIsoClassFunctor p).map f1)
        ((fiberIsoClassFunctor p).map f2) :=
  fun x ↦
    ⟨⟨(CategoricalPullback.π₁ (pushforwardFiberFunctor p χ f1)
          (pushforwardFiberFunctor p χ f2)).isoClassesMap x,
      (CategoricalPullback.π₂ (pushforwardFiberFunctor p χ f1)
          (pushforwardFiberFunctor p χ f2)).isoClassesMap x⟩,
      fiberProductIsoClassComparison_mem p χ f1 f2 x⟩

/-- The fibre 2-fibre product iso-class comparison sends a class to the pair of
its images under `π₁.isoClassesMap` and `π₂.isoClassesMap`. -/
theorem fiberProductIsoClassComparison_spec
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (χ : p.op.Cleavage) {A A1 A2 : ArtinianLocalAlgCat Λ k}
    (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (x : isomorphismClasses.obj
      (Cat.of ((pushforwardFiberFunctor p χ f1) ⊡ (pushforwardFiberFunctor p χ f2)))) :
    (fiberProductIsoClassComparison p χ f1 f2 x).1 =
      ((CategoricalPullback.π₁ (pushforwardFiberFunctor p χ f1)
          (pushforwardFiberFunctor p χ f2)).isoClassesMap x,
        (CategoricalPullback.π₂ (pushforwardFiberFunctor p χ f1)
          (pushforwardFiberFunctor p χ f2)).isoClassesMap x) :=
  sorry

/-- On a represented triple `⟨x1, x2, e⟩`, the comparison map is the pair of
represented classes `(Quotient.mk'' x1, Quotient.mk'' x2)`. -/
theorem fiberProductIsoClassComparison_mk
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (χ : p.op.Cleavage) {A A1 A2 : ArtinianLocalAlgCat Λ k}
    (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) (x1 : p.Fiber A1) (x2 : p.Fiber A2)
    (e : (pushforwardFiberFunctor p χ f1).obj x1 ≅
      (pushforwardFiberFunctor p χ f2).obj x2) :
    (fiberProductIsoClassComparison p χ f1 f2 (Quotient.mk'' ⟨x1, x2, e⟩)).1 =
      (Quotient.mk'' x1, Quotient.mk'' x2) :=
  sorry

end CategoryTheory.Functor
