/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.MeromorphicSection.Pullback
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure.Finiteness
public import ReasLib.AlgebraicGeometry.Scheme.MeromorphicFunction.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.EmbeddedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary

/-!
# Restrictions of meromorphic sections to irreducible components

This file packages an explicit restriction of a meromorphic section to the
reduced closure of an irreducible component, together with its regularity.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.MeromorphicSection

variable {X : Scheme.{u}}

/-- An explicit restriction of a meromorphic section to the reduced closure of
an irreducible component, with its pullback identity and regularity. -/
structure RegularComponentRestriction
    (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (C : irreducibleComponents X) where
  pullbackDefined :
    LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined
      (Scheme.PointClosure.ι (genericPoints.ofComponent C).1).toLRSHom
  section_ :
    (Scheme.PointClosure.scheme (genericPoints.ofComponent C).1).toLocallyRingedSpace.meromorphicSections
      ((Scheme.Modules.pullback
        (Scheme.PointClosure.ι (genericPoints.ofComponent C).1)).obj ℒ)
  pullback_eq : section_ =
    LocallyRingedSpace.Hom.pullbackMeromorphicSections
      (Scheme.PointClosure.ι (genericPoints.ofComponent C).1).toLRSHom
      pullbackDefined ℒ s
  regular :
    (Scheme.PointClosure.scheme (genericPoints.ofComponent C).1).toLocallyRingedSpace.IsRegularMeromorphicSection
      ((Scheme.Modules.pullback
        (Scheme.PointClosure.ι (genericPoints.ofComponent C).1)).obj ℒ) section_

namespace RegularComponentRestriction

/-- Build a component restriction from an explicitly supplied section and its
pullback and regularity laws. -/
def ofSection
    (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (C : irreducibleComponents X)
    (pullbackDefined :
      LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined
        (Scheme.PointClosure.ι (genericPoints.ofComponent C).1).toLRSHom)
    (section_ :
      (Scheme.PointClosure.scheme (genericPoints.ofComponent C).1).toLocallyRingedSpace.meromorphicSections
        ((Scheme.Modules.pullback
          (Scheme.PointClosure.ι (genericPoints.ofComponent C).1)).obj ℒ))
    (pullback_eq : section_ =
      LocallyRingedSpace.Hom.pullbackMeromorphicSections
        (Scheme.PointClosure.ι (genericPoints.ofComponent C).1).toLRSHom
        pullbackDefined ℒ s)
    (regular :
      (Scheme.PointClosure.scheme (genericPoints.ofComponent C).1).toLocallyRingedSpace.IsRegularMeromorphicSection
        ((Scheme.Modules.pullback
          (Scheme.PointClosure.ι (genericPoints.ofComponent C).1)).obj ℒ) section_) :
    RegularComponentRestriction ℒ s C :=
  { pullbackDefined, section_, pullback_eq, regular }

/-- The section stored by `ofSection` is the explicitly supplied component
section. -/
theorem ofSection_section
    (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (C : irreducibleComponents X)
    (pullbackDefined :
      LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined
        (Scheme.PointClosure.ι (genericPoints.ofComponent C).1).toLRSHom)
    (section_ :
      (Scheme.PointClosure.scheme (genericPoints.ofComponent C).1).toLocallyRingedSpace.meromorphicSections
        ((Scheme.Modules.pullback
          (Scheme.PointClosure.ι (genericPoints.ofComponent C).1)).obj ℒ))
    (pullback_eq : section_ =
      LocallyRingedSpace.Hom.pullbackMeromorphicSections
        (Scheme.PointClosure.ι (genericPoints.ofComponent C).1).toLRSHom
        pullbackDefined ℒ s)
    (regular :
      (Scheme.PointClosure.scheme (genericPoints.ofComponent C).1).toLocallyRingedSpace.IsRegularMeromorphicSection
        ((Scheme.Modules.pullback
          (Scheme.PointClosure.ι (genericPoints.ofComponent C).1)).obj ℒ) section_) :
    (ofSection ℒ s C pullbackDefined section_ pullback_eq regular).section_ =
      section_ := sorry

/-- A component restriction is the pulled-back section and is regular
meromorphic. -/
theorem spec
    (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (C : irreducibleComponents X) (r : RegularComponentRestriction ℒ s C) :
    r.section_ =
        LocallyRingedSpace.Hom.pullbackMeromorphicSections
          (Scheme.PointClosure.ι (genericPoints.ofComponent C).1).toLRSHom
          r.pullbackDefined ℒ s ∧
      (Scheme.PointClosure.scheme (genericPoints.ofComponent C).1).toLocallyRingedSpace.IsRegularMeromorphicSection
        ((Scheme.Modules.pullback
          (Scheme.PointClosure.ι (genericPoints.ofComponent C).1)).obj ℒ) r.section_ := sorry

/-- A regular meromorphic restriction to an integral component is nonzero. -/
theorem section_ne_zero
    (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (C : irreducibleComponents X) (r : RegularComponentRestriction ℒ s C) :
    r.section_ ≠ 0 := sorry

end RegularComponentRestriction
end AlgebraicGeometry.Scheme.Modules.MeromorphicSection

namespace AlgebraicGeometry.Scheme.Modules.DenominatorProduct

open MeromorphicSection

/-- Under the standard dimension, support, and regularity hypotheses, the
section has a regular restriction to every top-dimensional irreducible
component. -/
theorem exists_regularComponentRestrictions
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)
    (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hX : ∀ x, p.relativeDimensionFunction δ x ≤ k + 1)
    (hXEmbedded : X.embeddedPoints = ∅)
    (hFEmbedded : ℱ.embeddedAssociatedPoints = ∅)
    (hFSupport : RingedSpace.moduleSupport ℱ = Set.univ)
    (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s) :
    Nonempty (∀ C : irreducibleComponents X,
      p.relativeDimensionFunction δ (genericPoints.ofComponent C).1 = k + 1 →
        RegularComponentRestriction ℒ s C) := sorry

end AlgebraicGeometry.Scheme.Modules.DenominatorProduct
