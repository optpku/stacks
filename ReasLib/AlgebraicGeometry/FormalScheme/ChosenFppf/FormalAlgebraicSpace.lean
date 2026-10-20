/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalScheme.ChosenFppf.Points
public import ReasLib.AlgebraicGeometry.FormalScheme.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Basic
public import Mathlib.CategoryTheory.Equivalence

/-!
# Formal schemes as formal algebraic spaces

Over a terminal base, the points functor embeds bounded formal schemes into
formal algebraic spaces and is an equivalence onto its essential image.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.FormalScheme

/-- Over a terminal base, the points sheaf of a formal scheme is a formal
algebraic space when the chosen site is small bound-closed and bounds its size. -/
theorem isFormalAlgebraicSpace_sheafOfPoints
    (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (hS : IsTerminal (𝒮.toScheme.obj S))
    (h𝒮 : Scheme.IsSmallBoundClosed
      (fun T : Scheme.{u} ↦ ∃ U : 𝒮.carrier, Nonempty (T ≅ 𝒮.toScheme.obj U)))
    (X : FormalScheme.{u})
    (hsize : ∃ T : 𝒮.carrier, X.size ≤ (𝒮.toScheme.obj T).size) :
    IsFormalAlgebraicSpace ((sheafOfPoints 𝒮 S).obj X) :=
  sorry

/-- Over a terminal base, postcomposition induces a bijection on points-sheaf
morphisms when the chosen site is small bound-closed and bounds the source size. -/
theorem sheafOfPoints_map_bijective_of_size
    (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (hS : IsTerminal (𝒮.toScheme.obj S))
    (h𝒮 : Scheme.IsSmallBoundClosed
      (fun T : Scheme.{u} ↦ ∃ U : 𝒮.carrier, Nonempty (T ≅ 𝒮.toScheme.obj U)))
    {X Y : FormalScheme.{u}}
    (hsize : ∃ T : 𝒮.carrier, X.size ≤ (𝒮.toScheme.obj T).size) :
    Function.Bijective
      ((sheafOfPoints 𝒮 S).map :
        (X ⟶ Y) → ((sheafOfPoints 𝒮 S).obj X ⟶ (sheafOfPoints 𝒮 S).obj Y)) :=
  sorry

/-- The full subcategory of formal schemes whose size is bounded by a scheme
represented in the chosen site. -/
abbrev Bounded (𝒮 : ChosenBigFppfSite.{u, v}) :=
  ObjectProperty.FullSubcategory (fun X : FormalScheme.{u} ↦
    ∃ T : 𝒮.carrier, X.size ≤ (𝒮.toScheme.obj T).size)

/-- The points functor from bounded formal schemes to formal algebraic spaces
on a small bound-closed chosen site over a terminal base. -/
def formalAlgebraicSpaceOfPoints
    (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (hS : IsTerminal (𝒮.toScheme.obj S))
    (h𝒮 : Scheme.IsSmallBoundClosed
      (fun T : Scheme.{u} ↦ ∃ U : 𝒮.carrier, Nonempty (T ≅ 𝒮.toScheme.obj U))) :
    Bounded 𝒮 ⥤ ObjectProperty.FullSubcategory
      (fun F : Sheaf (𝒮.bigTopology S) (Type (max u v)) ↦ IsFormalAlgebraicSpace F) :=
  ObjectProperty.lift
    (fun F : Sheaf (𝒮.bigTopology S) (Type (max u v)) ↦ IsFormalAlgebraicSpace F)
    (ObjectProperty.ι (fun X : FormalScheme.{u} ↦
      ∃ T : 𝒮.carrier, X.size ≤ (𝒮.toScheme.obj T).size) ⋙ sheafOfPoints 𝒮 S)
    (fun X ↦ isFormalAlgebraicSpace_sheafOfPoints 𝒮 S hS h𝒮 X.obj X.property)

/-- The underlying sheaf of the lifted points functor is the original points
sheaf of the underlying formal scheme. -/
theorem formalAlgebraicSpaceOfPoints_obj
    (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (hS : IsTerminal (𝒮.toScheme.obj S))
    (h𝒮 : Scheme.IsSmallBoundClosed
      (fun T : Scheme.{u} ↦ ∃ U : 𝒮.carrier, Nonempty (T ≅ 𝒮.toScheme.obj U)))
    (X : Bounded 𝒮) :
    ((formalAlgebraicSpaceOfPoints 𝒮 S hS h𝒮).obj X).obj =
      (sheafOfPoints 𝒮 S).obj X.obj :=
  rfl

/-- Over a terminal base, the points functor identifies bounded formal schemes
with its full essential-image subcategory of formal algebraic spaces. -/
theorem formalAlgebraicSpaceOfPoints_toEssImage_isEquivalence
    (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (hS : IsTerminal (𝒮.toScheme.obj S))
    (h𝒮 : Scheme.IsSmallBoundClosed
      (fun T : Scheme.{u} ↦ ∃ U : 𝒮.carrier, Nonempty (T ≅ 𝒮.toScheme.obj U))) :
    (formalAlgebraicSpaceOfPoints 𝒮 S hS h𝒮).toEssImage.IsEquivalence :=
  sorry

end AlgebraicGeometry.FormalScheme
