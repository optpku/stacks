/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Complexes.Category
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory

/-!
# The groupoid fibration of relatively perfect complexes

The projection from admissible complexes on scheme-valued fibres to schemes
over the base is fibred in groupoids.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Complexes

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- For a proper, flat morphism `f : X ⟶ B` of finite presentation, the
projection from relatively perfect complexes on its scheme-valued fibres with
vanishing negative fibre self-Ext to `Over S` is fibred in groupoids. -/
instance instIsFiberedInGroupoids (f : X ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f] :
    Functor.IsFibered.InGroupoids (p f) := sorry

/-- The category of relatively perfect complexes on fibres of `f` with vanishing
negative fibre self-Ext, bundled as a category fibred in groupoids over `Over S`
with Hom-universe `u + 1`. -/
def toGroupoids (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f] :
    FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S) :=
  FiberedCategoryOver.Groupoids.ofFunctor.{u + 1, u, u + 1, u + 1} (p f)

/-- The projection of `toGroupoids f` is `p f`, sending each complex to its
underlying test scheme over `S`. -/
theorem toGroupoids_p (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f] :
    (toGroupoids f).p = p f := sorry

/-- The total category of `toGroupoids f` is `category f`, the category of
relatively perfect complexes on fibres with vanishing negative fibre self-Ext. -/
theorem toGroupoids_total (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f] :
    (toGroupoids f).total = category f := sorry

end AlgebraicGeometry.AlgebraicSpace.Complexes
