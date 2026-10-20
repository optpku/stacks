/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import ReasLib.AlgebraicGeometry.Scheme.Cover.AffineFamily
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Standard

/-!
# Standard finite affine covers

This leaf provides the common five-way standard-cover predicate used by
directed-affine approximation and extension arguments.  It is deliberately
separate from the concrete `StandardEtaleCover`, `StandardSmoothCovering`,
and related packages: an `AffineFamilyOver` is the canonical carrier for
refinements and base change, while the topology-specific condition remains a
small proposition on that carrier.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

noncomputable section

/-- The five standard topologies used for finite affine chart covers.

This is a finite index of topology-specific chart conditions, rather than a
second Grothendieck-topology interface.  The associated site topology is
defined in `Sites.Extension.Standard`.
-/
inductive StandardTopology where
  /-- The Zariski topology. -/
  | zariski
  /-- The etale topology. -/
  | etale
  /-- The smooth topology. -/
  | smooth
  /-- The syntomic topology. -/
  | syntomic
  /-- The fppf topology. -/
  | fppf

namespace AffineFamilyOver

variable {T : Scheme.{u}}

/-- The chart images of a finite affine family jointly cover its target. -/
def Covers (family : AffineFamilyOver T) : Prop :=
  ∀ t : T, ∃ j : Fin family.n,
    t ∈ Set.range ⇑(ConcreteCategory.hom (family.map j).base)

/-- The pointwise covering condition unfolds to the defining existential. -/
theorem covers_iff (family : AffineFamilyOver T) :
    family.Covers ↔
      ∀ t : T, ∃ j : Fin family.n,
        t ∈ Set.range ⇑(ConcreteCategory.hom (family.map j).base) := sorry

end AffineFamilyOver

namespace StandardTopology

variable {T : Scheme.{u}}

/-- The topology-specific condition on every chart of a finite affine family. -/
def ChartCondition (τ : StandardTopology) (family : AffineFamilyOver T) : Prop :=
  match τ with
  | zariski =>
      ∀ j : Fin family.n,
        IsOpenImmersion (family.map j) ∧
          ∃ s : Γ(T, ⊤),
            Set.range ⇑(ConcreteCategory.hom (family.map j).base) =
              (T.basicOpen s : Set T)
  | etale => ∀ j : Fin family.n, Etale (family.map j)
  | smooth =>
      ∀ j : Fin family.n,
        RingHom.IsStandardSmooth
          (CommRingCat.Hom.hom (Scheme.Hom.appTop (family.map j)))
  | syntomic =>
      ∀ j : Fin family.n,
        let f := CommRingCat.Hom.hom (Scheme.Hom.appTop (family.map j))
        @Algebra.IsRelativeGlobalCompleteIntersection _ _ _ _ f.toAlgebra
  | fppf =>
      ∀ j : Fin family.n,
        Flat (family.map j) ∧ LocallyOfFinitePresentation (family.map j)

/-- A finite affine family is a standard cover for the selected topology.

The target's affineness, joint surjectivity, and memberwise chart condition
are kept as separate conjuncts so that downstream arguments can project the
piece they need without unpacking a topology-specific wrapper.
-/
def IsCover (τ : StandardTopology) (family : AffineFamilyOver T) : Prop :=
  IsAffine T ∧ family.Covers ∧ τ.ChartCondition family

/-- The affine-target part of a standard-cover witness. -/
theorem IsCover.isAffine {τ : StandardTopology}
    {family : AffineFamilyOver T} (h : τ.IsCover family) :
    IsAffine T := sorry

/-- The joint-surjectivity part of a standard-cover witness. -/
theorem IsCover.covers {τ : StandardTopology}
    {family : AffineFamilyOver T} (h : τ.IsCover family) :
    family.Covers := sorry

/-- The memberwise topology-specific part of a standard-cover witness. -/
theorem IsCover.chartCondition {τ : StandardTopology}
    {family : AffineFamilyOver T} (h : τ.IsCover family) :
    τ.ChartCondition family := sorry

/-- The three defining components of a standard-cover witness. -/
theorem isCover_iff (τ : StandardTopology) (family : AffineFamilyOver T) :
    τ.IsCover family ↔ IsAffine T ∧ family.Covers ∧ τ.ChartCondition family := sorry

end StandardTopology

end

end AlgebraicGeometry
