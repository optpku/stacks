/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.DeterminantComparison
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Locality
public import ReasLib.AlgebraicGeometry.Scheme.Pullback.Opens

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeDifferentials

open PerfectDerived.TorNegOneZero.Determinant

/-- A pair of comparison-map families satisfying the unit, wedge, and base-change
compatibility conditions for an open-pullback square. -/
structure CompatibleComparison
    {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a)
    [h_open : IsOpenImmersion (pullback.lift b f' sq.w)]
    [h_quasiFinite : LocallyQuasiFinite f] [h_syntomic : Syntomic f]
    (P : Pullback b) where
  /-- The comparison family on the right edge. -/
  source : ∀ p : ℕ,
    (Λ[p] Ω[(terminal.from Y).toShHom]) ⟶
      (Scheme.Modules.pullback f).obj (Λ[p] Ω[(terminal.from X).toShHom]) ⊗
        P.source.line (naiveCotangentObject f)
  /-- The comparison family on the left edge. -/
  target : ∀ p : ℕ,
    (Λ[p] Ω[(terminal.from Y').toShHom]) ⟶
      (Scheme.Modules.pullback f').obj (Λ[p] Ω[(terminal.from X').toShHom]) ⊗
        P.target.line (baseChangedNaiveCotangentObject b f' f a sq)
  /-- The source family maps the exterior unit to the discriminant section. -/
  sourceMapsUnit : MapsUnitToDiscriminant f P.source source
  /-- The source family is compatible with wedge multiplication. -/
  sourceWedge : CompatibleWithWedge f P.source source
  /-- The target family maps the exterior unit to the base-changed discriminant section. -/
  targetMapsUnit : BaseChangedMapsUnitToDiscriminant b f' f a sq P.target target
  /-- The target family is compatible with wedge multiplication. -/
  targetWedge : BaseChangedCompatibleWithWedge b f' f a sq P.target target
  /-- The two comparison families commute with the canonical base-change map in every degree. -/
  naturality : ∀ p : ℕ,
    (Scheme.Modules.pullback b).map (source p) ≫
        comparisonTargetMap b f' f a sq P p =
      absoluteFormComparison b p ≫ target p

namespace CompatibleComparison

/-- Build compatible comparison data from two concrete map families and their laws. -/
def ofMaps
    {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)]
    [LocallyQuasiFinite f] [Syntomic f] (P : Pullback b)
    (source : ∀ p : ℕ,
      (Λ[p] Ω[(terminal.from Y).toShHom]) ⟶
        (Scheme.Modules.pullback f).obj (Λ[p] Ω[(terminal.from X).toShHom]) ⊗
          P.source.line (naiveCotangentObject f))
    (target : ∀ p : ℕ,
      (Λ[p] Ω[(terminal.from Y').toShHom]) ⟶
        (Scheme.Modules.pullback f').obj (Λ[p] Ω[(terminal.from X').toShHom]) ⊗
          P.target.line (baseChangedNaiveCotangentObject b f' f a sq))
    (sourceMapsUnit : MapsUnitToDiscriminant f P.source source)
    (sourceWedge : CompatibleWithWedge f P.source source)
    (targetMapsUnit : BaseChangedMapsUnitToDiscriminant b f' f a sq P.target target)
    (targetWedge : BaseChangedCompatibleWithWedge b f' f a sq P.target target)
    (naturality : ∀ p : ℕ,
      (Scheme.Modules.pullback b).map (source p) ≫
          comparisonTargetMap b f' f a sq P p =
        absoluteFormComparison b p ≫ target p) :
    CompatibleComparison b f' f a sq P where
  source := source
  target := target
  sourceMapsUnit := sourceMapsUnit
  sourceWedge := sourceWedge
  targetMapsUnit := targetMapsUnit
  targetWedge := targetWedge
  naturality := naturality

/-- The source family of a compatible comparison satisfies the unit and wedge conditions. -/
theorem source_spec
    {X' X Y' Y : Scheme.{u}}
    {b : Y' ⟶ Y} {f' : Y' ⟶ X'} {f : Y ⟶ X} {a : X' ⟶ X}
    {sq : CommSq b f' f a} [IsOpenImmersion (pullback.lift b f' sq.w)]
    [LocallyQuasiFinite f] [Syntomic f] {P : Pullback b}
    (C : CompatibleComparison b f' f a sq P) :
    MapsUnitToDiscriminant f P.source C.source ∧
      CompatibleWithWedge f P.source C.source := sorry

/-- The target family of a compatible comparison satisfies the unit and wedge conditions. -/
theorem target_spec
    {X' X Y' Y : Scheme.{u}}
    {b : Y' ⟶ Y} {f' : Y' ⟶ X'} {f : Y ⟶ X} {a : X' ⟶ X}
    {sq : CommSq b f' f a} [IsOpenImmersion (pullback.lift b f' sq.w)]
    [LocallyQuasiFinite f] [Syntomic f] {P : Pullback b}
    (C : CompatibleComparison b f' f a sq P) :
    BaseChangedMapsUnitToDiscriminant b f' f a sq P.target C.target ∧
      BaseChangedCompatibleWithWedge b f' f a sq P.target C.target := sorry

end CompatibleComparison

/-- Around every point in the upper-left scheme of an open-pullback square with locally
quasi-finite syntomic right edge, compatible comparison maps exist on suitable open
restrictions for every determinant pullback datum. -/
theorem exists_localCompatibleComparison
    {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)]
    [LocallyQuasiFinite f] [Syntomic f] (y' : Y') :
    ∃ (V' : Y'.Opens) (V : Y.Opens) (U' : X'.Opens) (U : X.Opens),
      ∃ (hy' : y' ∈ V')
        (hb : V' ≤ b ⁻¹ᵁ V) (hf' : V' ≤ f' ⁻¹ᵁ U')
        (ha : U' ≤ a ⁻¹ᵁ U) (hf : V ≤ f ⁻¹ᵁ U),
        ∀ P : Pullback (b.resLE V V' hb),
          Nonempty (CompatibleComparison
            (h_open := Scheme.Pullback.restrictedLiftIsOpenImmersion
              b f' f a sq V' V U' U hb hf' hf ha)
            (h_syntomic := Scheme.Hom.syntomic_resLE_of_syntomic f (inferInstance) hf)
            (b.resLE V V' hb) (f'.resLE U' V' hf')
            (f.resLE U V hf) (a.resLE U U' ha)
            (Scheme.Pullback.restrictedCommSq
              b f' f a sq V' V U' U hb hf' hf ha) P) := sorry

end AlgebraicGeometry.Scheme.RelativeDifferentials
