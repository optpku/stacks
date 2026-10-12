/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.DeterminantComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.Tate
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.RegularSection.Tensor

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme.RelativeDifferentials

namespace CanonicalComparison

/-- The comparison family with values in the fixed determinant of the naive cotangent complex. -/
abbrev Family {X Y : Scheme.{u}} (f : Y ⟶ X) [Syntomic f] :=
  ∀ p : ℕ, (Λ[p] Ω[(terminal.from Y).toShHom]) ⟶
    (Scheme.Modules.pullback f).obj (Λ[p] Ω[(terminal.from X).toShHom]) ⊗ ActualTate.detNL f

/-- The exterior unit on the base, pulled back to the source. -/
def pulledBackUnit {X Y : Scheme.{u}} (f : Y ⟶ X) :
    SheafOfModules.RingedSite.unitModule (Opens.grothendieckTopology Y) Y.sheaf ⟶
      (Scheme.Modules.pullback f).obj (Λ[0] Ω[(terminal.from X).toShHom]) :=
  (RingedSpace.unitIsoTensorUnit Y.toRingedSpace).hom ≫
    (Scheme.Modules.pullbackUnitIso f).inv ≫
    (Scheme.Modules.pullback f).map
      ((RingedSpace.unitIsoTensorUnit X.toRingedSpace).inv ≫
        SheafOfModules.RingedSite.ExteriorPower.one X.sheaf Ω[(terminal.from X).toShHom])

/-- The degree-zero target element is the pulled-back exterior unit tensored with delta. -/
def unitTarget {X Y : Scheme.{u}} (f : Y ⟶ X) [LocallyQuasiFinite f] [Syntomic f] :
    SheafOfModules.RingedSite.unitModule (Opens.grothendieckTopology Y) Y.sheaf ⟶
      (Scheme.Modules.pullback f).obj (Λ[0] Ω[(terminal.from X).toShHom]) ⊗ ActualTate.detNL f :=
  pulledBackUnit f ≫
    RingedSpace.tensorSectionHom
      ((Scheme.Modules.pullback f).obj (Λ[0] Ω[(terminal.from X).toShHom]))
      (ActualTate.detNL f) (ActualTate.delta f)

/-- Degree zero sends one to the canonical determinant section. -/
def MapsUnitToDiscriminant {X Y : Scheme.{u}} (f : Y ⟶ X)
    [LocallyQuasiFinite f] [Syntomic f] (c : Family f) : Prop :=
  SheafOfModules.RingedSite.ExteriorPower.one Y.sheaf Ω[(terminal.from Y).toShHom] ≫ c 0 =
    unitTarget f

/-- Compatibility with left wedge multiplication by pulled-back absolute forms. -/
def CompatibleWithWedge {X Y : Scheme.{u}} (f : Y ⟶ X) [Syntomic f] (c : Family f) : Prop :=
  ∀ q p : ℕ,
    tensorHom (absoluteFormComparison f q) (𝟙 (Λ[p] Ω[(terminal.from Y).toShHom])) ≫
        SheafOfModules.RingedSite.ExteriorPower.mul Y.sheaf Ω[(terminal.from Y).toShHom] q p ≫
        c (q + p) =
      ((Scheme.Modules.pullback f).obj (Λ[q] Ω[(terminal.from X).toShHom]) ◁ c p) ≫
        (α_ ((Scheme.Modules.pullback f).obj (Λ[q] Ω[(terminal.from X).toShHom]))
          ((Scheme.Modules.pullback f).obj (Λ[p] Ω[(terminal.from X).toShHom]))
          (ActualTate.detNL f)).inv ≫
        (pullbackAbsoluteWedge f q p ▷ ActualTate.detNL f)

/-- The target comparison uses pullback monoidality, the actual absolute-form
comparison, and the fixed determinant base-change map. -/
def targetMap {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)]
    [Syntomic f] [Syntomic f'] (p : ℕ) :
    (Scheme.Modules.pullback b).obj
        ((Scheme.Modules.pullback f).obj (Λ[p] Ω[(terminal.from X).toShHom]) ⊗ ActualTate.detNL f) ⟶
      (Scheme.Modules.pullback f').obj (Λ[p] Ω[(terminal.from X').toShHom]) ⊗ ActualTate.detNL f' :=
  Scheme.Modules.pullbackTensorComparison b _ _ ≫
    tensorHom (targetAbsoluteFormComparison b f' f a sq p) (ActualTate.baseChangeIso b f' f a sq).hom

/-- The target map is pullback tensor comparison followed by the absolute-form and determinant comparisons. -/
theorem targetMap_spec {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)]
    [Syntomic f] [Syntomic f'] (p : ℕ) :
    targetMap b f' f a sq p = Scheme.Modules.pullbackTensorComparison b _ _ ≫
      tensorHom (targetAbsoluteFormComparison b f' f a sq p)
        (ActualTate.baseChangeIso b f' f a sq).hom := rfl

end CanonicalComparison

/-- A degreewise comparison rule for locally quasi-finite syntomic morphisms of arbitrary schemes. -/
structure ComparisonRule where
  /-- The determinant-valued comparison in every exterior degree. -/
  component : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
    [LocallyQuasiFinite f] [Syntomic f], CanonicalComparison.Family f

namespace ComparisonRule

/-- Construct a comparison rule from its complete family of components. -/
def ofComponents
    (component : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
      [LocallyQuasiFinite f] [Syntomic f], CanonicalComparison.Family f) : ComparisonRule.{u} :=
  ⟨component⟩

/-- Evaluating the rule constructed from a family recovers that family's component. -/
theorem ofComponents_apply
    (component : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
      [LocallyQuasiFinite f] [Syntomic f], CanonicalComparison.Family f)
    {X Y : Scheme.{u}} (f : Y ⟶ X) [LocallyQuasiFinite f] [Syntomic f] (p : ℕ) :
    (ofComponents component).component f p = component f p := rfl

/-- Two comparison rules agree when all their components agree. -/
theorem ext (r₁ r₂ : ComparisonRule.{u})
    (h : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
      [LocallyQuasiFinite f] [Syntomic f] (p : ℕ), r₁.component f p = r₂.component f p) :
    r₁ = r₂ := sorry

end ComparisonRule

/-- Unit normalization, wedge compatibility, and canonical open-base-change naturality. -/
structure IsComparisonRule (r : ComparisonRule.{u}) : Prop where
  mapsUnit : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [LocallyQuasiFinite f] [Syntomic f],
    CanonicalComparison.MapsUnitToDiscriminant f (r.component f)
  wedge : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [LocallyQuasiFinite f] [Syntomic f],
    CanonicalComparison.CompatibleWithWedge f (r.component f)
  naturality : ∀ {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)]
    [LocallyQuasiFinite f] [Syntomic f] [LocallyQuasiFinite f'] [Syntomic f'] (p : ℕ),
    (Scheme.Modules.pullback b).map (r.component f p) ≫ CanonicalComparison.targetMap b f' f a sq p =
      absoluteFormComparison b p ≫ r.component f' p

namespace IsComparisonRule

/-- Construct the comparison-rule predicate from unit, wedge and open-base-change laws. -/
def ofProperties (r : ComparisonRule.{u})
    (mapsUnit : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [LocallyQuasiFinite f] [Syntomic f],
      CanonicalComparison.MapsUnitToDiscriminant f (r.component f))
    (wedge : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [LocallyQuasiFinite f] [Syntomic f],
      CanonicalComparison.CompatibleWithWedge f (r.component f))
    (naturality : ∀ {X' X Y' Y : Scheme.{u}}
      (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
      (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)]
      [LocallyQuasiFinite f] [Syntomic f] [LocallyQuasiFinite f'] [Syntomic f'] (p : ℕ),
      (Scheme.Modules.pullback b).map (r.component f p) ≫ CanonicalComparison.targetMap b f' f a sq p =
        absoluteFormComparison b p ≫ r.component f' p) : IsComparisonRule r :=
  ⟨mapsUnit, wedge, naturality⟩

/-- A comparison rule satisfies both unit normalization and wedge compatibility on each morphism. -/
theorem component_spec {r : ComparisonRule.{u}} (hr : IsComparisonRule r)
    {X Y : Scheme.{u}} (f : Y ⟶ X) [LocallyQuasiFinite f] [Syntomic f] :
    CanonicalComparison.MapsUnitToDiscriminant f (r.component f) ∧
      CanonicalComparison.CompatibleWithWedge f (r.component f) :=
  ⟨hr.mapsUnit f, hr.wedge f⟩

end IsComparisonRule

/-- There is a unique normalized determinant-valued comparison rule on locally quasi-finite syntomic morphisms of schemes. -/
theorem existsUniqueComparisonRule : ∃! r : ComparisonRule.{u}, IsComparisonRule r := sorry

namespace ComparisonRule

/-- Pulling back an absolute form and then applying the comparison is tensor multiplication by delta. -/
theorem absoluteFormComparison_comp_component
    (r : ComparisonRule.{u}) (hr : IsComparisonRule r)
    {X Y : Scheme.{u}} (f : Y ⟶ X) [LocallyQuasiFinite f] [Syntomic f] (p : ℕ) :
    absoluteFormComparison f p ≫ r.component f p =
      RingedSpace.tensorSectionHom
        ((Scheme.Modules.pullback f).obj (Λ[p] Ω[(terminal.from X).toShHom]))
        (ActualTate.detNL f) (ActualTate.delta f) := sorry

end ComparisonRule

end Scheme.RelativeDifferentials
end AlgebraicGeometry
