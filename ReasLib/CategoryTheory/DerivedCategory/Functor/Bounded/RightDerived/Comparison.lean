/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Bounded.SingleFunctor.Localization
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounded-Below Right-Derived Comparisons

This leaf owns the degree functors and the degree-zero comparison for a chosen
bounded-below right-derived model.  The reusable all-degree single-object and
localization-model comparisons live in
`DerivedCategory.Bounded.SingleFunctor.Localization`.
-/

open CategoryTheory
open scoped CategoryTheory

noncomputable section

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

section RightDerived

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w₁} 𝒜] [HasDerivedCategory.{w₂} ℬ]

/-- Stacks 015A: the degree-`i` bounded-below right derived functor attached
to `RF : D⁺(𝒜) ⥤ D⁺(ℬ)`, evaluated on the localization-model degree-zero
embedding. -/
@[stacks 015A]
abbrev RightDerived.degree (RF : DerivedCategory.Plus 𝒜 ⥤ DerivedCategory.Plus ℬ)
    (i : ℤ) : 𝒜 ⥤ ℬ :=
  DerivedCategory.Plus.singleFunctor 𝒜 0 ⋙ RF ⋙
    DerivedCategory.Plus.homologyFunctor ℬ i

namespace RightDerived.degree

/-- The degree functor computed with the localization-model single object is canonically
isomorphic to the degree functor defined using Mathlib's bounded-below single functor. -/
@[stacks 015A "bounded-below right-derived degree model comparison"]
noncomputable def fromHomotopyIso
    (RF : DerivedCategory.Plus 𝒜 ⥤ DerivedCategory.Plus ℬ) (i : ℤ) :
    DerivedCategory.Plus.singleFunctor.fromHomotopy 𝒜 0 ⋙ RF ⋙
        DerivedCategory.Plus.homologyFunctor ℬ i ≅
      RightDerived.degree RF i :=
  Functor.isoWhiskerRight
    (DerivedCategory.Plus.singleFunctor.fromHomotopy.iso 𝒜 0)
    (RF ⋙ DerivedCategory.Plus.homologyFunctor ℬ i)

end RightDerived.degree

end RightDerived

section DegreeZeroComparison

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w₁} 𝒜] [HasDerivedCategory.{w₂} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]
  (RF : DerivedCategory.Plus 𝒜 ⥤ DerivedCategory.Plus ℬ)
  (α : F.toBoundedBelowDerived ⟶ DerivedCategory.Plus.Qh ⋙ RF)

/-- The canonical degree-zero comparison from an additive functor to the
degree-zero functor obtained from a chosen bounded-below right derived model. -/
@[stacks 015A]
noncomputable def RightDerived.zero :
    F ⟶ RightDerived.degree RF 0 :=
  (Functor.isoWhiskerLeft F
      (DerivedCategory.singleFunctorCompHomologyFunctorIso ℬ 0).symm).hom ≫
    Functor.whiskerRight
      ((toBoundedBelowDerived.singleIso F 0).inv ≫
        Functor.whiskerRight
          (Functor.whiskerLeft (HomotopyCategory.Plus.singleFunctor 𝒜 0) α)
          DerivedCategory.Plus.ι)
      (DerivedCategory.homologyFunctor ℬ 0) ≫
    (RightDerived.degree.fromHomotopyIso RF 0).hom

namespace RightDerived.zero

/-- Naturality of the degree-zero right-derived comparison in component form. -/
@[reassoc (attr := simp), stacks 015A "bounded-below right-derived comparison naturality"]
theorem naturality {X Y : 𝒜} (f : X ⟶ Y) :
    F.map f ≫ (RightDerived.zero F RF α).app Y =
      (RightDerived.zero F RF α).app X ≫ (RightDerived.degree RF 0).map f := sorry

end RightDerived.zero

end DegreeZeroComparison

end Functor


end CategoryTheory
