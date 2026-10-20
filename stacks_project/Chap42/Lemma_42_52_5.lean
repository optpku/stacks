/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocalizedChern.Triangulated
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.LocalizedChern

open RingedSpace.ModuleDerived.Morphism

/- Lemma 42.52.5: localized Newton classes are additive in every integer degree on a
distinguished triangle of perfect objects supported on a closed center. -/
@[stacks 0FBE] #check (AlgebraicGeometry.LocalizedChern.newtonClass_distinguished :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom]
    {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (T : Triangle (RingedSpace.ModuleDerived X.left.toRingedSpace))
    (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.left.toRingedSpace))
    (h1 : RingedSpace.ModuleDerived.IsPerfect T.obj₁)
    (h2 : RingedSpace.ModuleDerived.IsPerfect T.obj₂)
    (h3 : RingedSpace.ModuleDerived.IsPerfect T.obj₃)
    (vanishing1 : IsZero (restrictAway i T.obj₁))
    (vanishing3 : IsZero (restrictAway i T.obj₃))
    (hfin :
        (∃ (Y : Scheme.{u}) (f : Y ⟶ X.left),
            IsEnvelope f ∧
              HasLocallyBoundedFiniteLocallyFree
                ((RingedSpace.modulePullbackDerived f.toShHom).map T.mor₃)) ∨
          HasLocallyBoundedFiniteLocallyFree T.mor₃ ∨
          (∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left)) ∨
          CompactSpace X.left)
    (classes : ChernClass.Theory δ X.hom)
    (finiteness1 : TechnicalCondition X T.obj₁)
    (finiteness2 : TechnicalCondition X T.obj₂)
    (finiteness3 : TechnicalCondition X T.obj₃)
    (p : ℤ),
    newtonClassInteger i classes T.obj₂ h2
        (restrictAway_obj₂_isZero i T hT vanishing1 vanishing3) finiteness2 p =
      BivariantClass.pointwiseAdd δ
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) p
        (newtonClassInteger i classes T.obj₁ h1 vanishing1 finiteness1 p)
        (newtonClassInteger i classes T.obj₃ h3 vanishing3 finiteness3 p))

/- The localized Chern character consequence of Lemma 42.52.5. -/
@[stacks 0FBE] #check (AlgebraicGeometry.LocalizedChern.rationalCharacter_distinguished :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom]
    {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (T : Triangle (RingedSpace.ModuleDerived X.left.toRingedSpace))
    (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.left.toRingedSpace))
    (h1 : RingedSpace.ModuleDerived.IsPerfect T.obj₁)
    (h2 : RingedSpace.ModuleDerived.IsPerfect T.obj₂)
    (h3 : RingedSpace.ModuleDerived.IsPerfect T.obj₃)
    (vanishing1 : IsZero (restrictAway i T.obj₁))
    (vanishing3 : IsZero (restrictAway i T.obj₃))
    (hfin :
        (∃ (Y : Scheme.{u}) (f : Y ⟶ X.left),
            IsEnvelope f ∧
              HasLocallyBoundedFiniteLocallyFree
                ((RingedSpace.modulePullbackDerived f.toShHom).map T.mor₃)) ∨
          HasLocallyBoundedFiniteLocallyFree T.mor₃ ∨
          (∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left)) ∨
          CompactSpace X.left)
    (classes : ChernClass.Theory δ X.hom)
    (finiteness1 : TechnicalCondition X T.obj₁)
    (finiteness2 : TechnicalCondition X T.obj₂)
    (finiteness3 : TechnicalCondition X T.obj₃),
    rationalCharacter i classes T.obj₂ h2
        (restrictAway_obj₂_isZero i T hT vanishing1 vanishing3) finiteness2 =
      fun p ↦ rationalCharacter i classes T.obj₁ h1 vanishing1 finiteness1 p +
        rationalCharacter i classes T.obj₃ h3 vanishing3 finiteness3 p)

end AlgebraicGeometry.LocalizedChern
