/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Yoneda
import StacksCheckRecall

@[expose] public section


universe u₁ u₂ v₁ v₂

namespace CategoryTheory.Limits

variable {I : Type u₁} [Category.{v₁} I]
variable {C : Type u₂} [Category.{v₂} C]

/- The source needs componentwise Type-valued Hom formulas and their Yoneda uniqueness
consequence. The verified candidates are `limit.homIso'`, `colimit.homIso'`, the less explicit
`IsLimit.homEquiv` and `IsColimit.homEquiv`, the stronger (co)yoneda limit-preservation instances,
and `Yoneda.ext`/`Coyoneda.ext`; nearby Definitions 4.14.1 and 4.14.2 likewise recall canonical
limit owners directly. The primed Hom isomorphisms are the best source-facing representation
because their compatible families are exactly the concrete limits of sets used in the remark.
Their `ULift` is only universe bookkeeping, so the textbook equalities are recovered as canonical
equivalences with no change to the diagram or test object. The two extensionality owners then give
the stated determination up to isomorphism, while keeping the standard APIs directly reusable. -/

section LimitHomIso

variable (M : I ⥤ C) [HasLimit M] (W : C)

/- Remark 4.14.4 (1): `limit.homIso'` identifies maps `W ⟶ limit M` with compatible families
`p_i : W ⟶ M.obj i`, the concrete limit in `Type` of the component Hom-sets. -/
@[stacks 002H "limit Hom-set as compatible cone components"]
#check (limit.homIso' M W :
  ULift.{u₁} (W ⟶ limit M : Type v₂) ≅
    { p : ∀ i, W ⟶ M.obj i //
      ∀ {i i' : I} (f : i ⟶ i'), p i ≫ M.map f = p i' })

end LimitHomIso

section ColimitHomIso

variable (M : I ⥤ C) [HasColimit M] (W : C)

/- Remark 4.14.4 (2): `colimit.homIso'` identifies maps `colimit M ⟶ W` with compatible families
`p_i : M.obj i ⟶ W`, the concrete limit over the opposite indexing category in `Type`. -/
@[stacks 002H "colimit Hom-set as compatible cocone components"]
#check (colimit.homIso' M W :
  ULift.{u₁} (colimit M ⟶ W : Type v₂) ≅
    { p : ∀ i, M.obj i ⟶ W //
      ∀ {i i' : I} (f : i ⟶ i'), M.map f ≫ p i' = p i })

end ColimitHomIso

section Ext

variable (X Y : C)
variable (p : ∀ {Z : C}, (Z ⟶ X) → (Z ⟶ Y))
variable (q : ∀ {Z : C}, (Z ⟶ Y) → (Z ⟶ X))
variable (h₁ : ∀ {Z : C} (f : Z ⟶ X), q (p f) = f)
variable (h₂ : ∀ {Z : C} (f : Z ⟶ Y), p (q f) = f)
variable (n : ∀ {Z Z' : C} (f : Z' ⟶ Z) (g : Z ⟶ X), p (f ≫ g) = f ≫ p g)

/- Remark 4.14.4 (3): `Yoneda.ext` expresses that the natural family of contravariant Hom-set
equivalences in (1) determines the limit object up to isomorphism. -/
@[stacks 002H "limit object determined by its contravariant Hom-functor"]
#check (Yoneda.ext X Y p q h₁ h₂ n : X ≅ Y)

variable (pCov : ∀ {Z : C}, (X ⟶ Z) → (Y ⟶ Z))
variable (qCov : ∀ {Z : C}, (Y ⟶ Z) → (X ⟶ Z))
variable (hCov₁ : ∀ {Z : C} (f : X ⟶ Z), qCov (pCov f) = f)
variable (hCov₂ : ∀ {Z : C} (f : Y ⟶ Z), pCov (qCov f) = f)
variable (nCov : ∀ {Z Z' : C} (f : Y ⟶ Z) (g : Z ⟶ Z'),
  qCov (f ≫ g) = qCov f ≫ g)

/- Remark 4.14.4 (4): `Coyoneda.ext` dually expresses that the natural family of covariant Hom-set
equivalences in (2) determines the colimit object up to isomorphism. -/
@[stacks 002H "colimit object determined by its covariant Hom-functor"]
#check (Coyoneda.ext X Y pCov qCov hCov₁ hCov₂ nCov : X ≅ Y)

end Ext

end CategoryTheory.Limits
