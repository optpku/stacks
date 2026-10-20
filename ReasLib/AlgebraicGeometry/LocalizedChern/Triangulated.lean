/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocalizedChern.Classes
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Representative.Morphism

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

open RingedSpace.ModuleDerived.Morphism

/-- If the first and third vertices of a distinguished triangle restrict to zero away from a
closed center, then the middle vertex also restricts to zero there. -/
theorem restrictAway_obj₂_isZero
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (T : Triangle (RingedSpace.ModuleDerived X.toRingedSpace))
    (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.toRingedSpace))
    (vanishing1 : IsZero (restrictAway i T.obj₁))
    (vanishing3 : IsZero (restrictAway i T.obj₃)) :
    IsZero (restrictAway i T.obj₂) := sorry

variable {S : Scheme.{u}} [UniversallyCatenary S]
variable {δ : S → ℤ} [IsDimensionFunction δ]
variable {X : Over S} [LocallyOfFiniteType X.hom]
variable {Z : Scheme.{u}}
variable (i : Z ⟶ X.left) [IsClosedImmersion i]
variable (T : Triangle (RingedSpace.ModuleDerived X.left.toRingedSpace))
variable (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.left.toRingedSpace))
variable (h1 : RingedSpace.ModuleDerived.IsPerfect T.obj₁)
variable (h2 : RingedSpace.ModuleDerived.IsPerfect T.obj₂)
variable (h3 : RingedSpace.ModuleDerived.IsPerfect T.obj₃)
variable (vanishing1 : IsZero (restrictAway i T.obj₁))
variable (vanishing3 : IsZero (restrictAway i T.obj₃))
variable (hfin :
    (∃ (Y : Scheme.{u}) (f : Y ⟶ X.left),
        IsEnvelope f ∧
          HasLocallyBoundedFiniteLocallyFree
            ((RingedSpace.modulePullbackDerived f.toShHom).map T.mor₃)) ∨
      HasLocallyBoundedFiniteLocallyFree T.mor₃ ∨
      (∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left)) ∨
      CompactSpace X.left)

include hT h1 h2 h3 vanishing1 vanishing3 hfin

/-- Localized Newton classes in every integer degree are additive on distinguished triangles
of perfect objects supported on a closed center, under the connecting-map finiteness alternatives. -/
theorem newtonClass_distinguished
    (classes : ChernClass.Theory δ X.hom)
    (finiteness1 : TechnicalCondition X T.obj₁)
    (finiteness2 : TechnicalCondition X T.obj₂)
    (finiteness3 : TechnicalCondition X T.obj₃)
    (p : ℤ) :
    newtonClassInteger i classes T.obj₂ h2
        (restrictAway_obj₂_isZero i T hT vanishing1 vanishing3) finiteness2 p =
      BivariantClass.pointwiseAdd δ
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) p
        (newtonClassInteger i classes T.obj₁ h1 vanishing1 finiteness1 p)
        (newtonClassInteger i classes T.obj₃ h3 vanishing3 finiteness3 p) := sorry

/-- Localized rational Chern characters are additive on distinguished triangles of perfect
objects supported on a closed center, under the connecting-map finiteness alternatives. -/
theorem rationalCharacter_distinguished
    (classes : ChernClass.Theory δ X.hom)
    (finiteness1 : TechnicalCondition X T.obj₁)
    (finiteness2 : TechnicalCondition X T.obj₂)
    (finiteness3 : TechnicalCondition X T.obj₃) :
    rationalCharacter i classes T.obj₂ h2
        (restrictAway_obj₂_isZero i T hT vanishing1 vanishing3) finiteness2 =
      fun p ↦ rationalCharacter i classes T.obj₁ h1 vanishing1 finiteness1 p +
        rationalCharacter i classes T.obj₃ h3 vanishing3 finiteness3 p := sorry

end AlgebraicGeometry.LocalizedChern
