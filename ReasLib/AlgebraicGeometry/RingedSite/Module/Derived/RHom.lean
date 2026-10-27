/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.Derived
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic

/-!
# Global derived Hom on a ringed site

This file owns the global `D(ℤ)`-valued derived Hom bifunctor for module sheaves on a ringed site.
Its existence is inherited from the reusable Grothendieck-abelian cochain-complex owner, so
downstream users only supply the ringed site and its canonical categorical structure.

The owner is independent of any chosen complex or tensor realization. Downstream tensor
comparisons should compose their derived tensor functor with `RHom.functor` in both variables.
-/

@[expose] public section

noncomputable section

universe z u v w

open CategoryTheory
-- Local instance justification (defeq pin): the generic ringed-site ModuleCat derived owner is
-- required by the derived-category APIs in this presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace RingedSite.Hom.ModuleDerived.RHom

variable (X : RingedSite.{u, v, w}) [UnivLE.{max u v, z}]

/-- The homotopy-level global enriched Hom bifunctor on complexes of `X`-modules. -/
@[stacks 0CS6 "homotopy-level global Hom bifunctor"]
noncomputable abbrev source :=
  CategoryTheory.CochainComplex.Enriched.RHom.source
    (C := ModuleCat.{z} X)

/-- The simultaneous quasi-isomorphism system for global derived Hom on `X`. -/
@[stacks 0CS6 "global Hom product quasi-isomorphisms"]
abbrev qis :=
  CategoryTheory.CochainComplex.Enriched.RHom.qis
    (C := ModuleCat.{z} X)

/-- The product localization from homotopy pairs of complexes of `X`-modules to derived
pairs. -/
@[stacks 0CS6 "global Hom product localization"]
noncomputable abbrev localization :=
  CategoryTheory.CochainComplex.Enriched.RHom.localization
    (C := ModuleCat.{z} X)

/-- The existence condition for global derived Hom of module sheaves on `X`. -/
@[stacks 0CS6 "existence condition for global derived Hom"]
abbrev Has : Prop :=
  CategoryTheory.CochainComplex.Enriched.RHom.Has (C := ModuleCat.{z} X)

variable [Has X]

/-- The global `D(ℤ)`-valued derived Hom bifunctor of module sheaves on `X`. -/
@[stacks 0CS6 "global derived Hom on a ringed site"]
noncomputable abbrev functor :=
  CategoryTheory.CochainComplex.Enriched.RHom.functor
    (C := ModuleCat.{z} X)

/-- The curried global derived-Hom functor, with the source variable first. -/
@[stacks 0CS6 "curried global derived Hom on a ringed site"]
noncomputable abbrev curried :=
  CategoryTheory.CochainComplex.Enriched.RHom.curried
    (C := ModuleCat.{z} X)

/-- Global derived Hom with fixed target and varying source. -/
@[stacks 0CS6 "source-variable global derived Hom on a ringed site"]
noncomputable abbrev sourceFunctor
    (N : DerivedCategory (ModuleCat.{z} X)) :=
  CategoryTheory.CochainComplex.Enriched.RHom.sourceFunctor
    (C := ModuleCat.{z} X) N

/-- Global derived Hom with fixed source and varying target. -/
@[stacks 0CS6 "target-variable global derived Hom on a ringed site"]
noncomputable abbrev targetFunctor
    (M : (DerivedCategory (ModuleCat.{z} X))ᵒᵖ) :=
  CategoryTheory.CochainComplex.Enriched.RHom.targetFunctor
    (C := ModuleCat.{z} X) M

/-- The universal map from the global Hom complex on homotopy objects to global derived Hom. -/
@[stacks 0CS6 "global Hom to global derived Hom"]
noncomputable abbrev unit :=
  CategoryTheory.CochainComplex.Enriched.RHom.unit
    (C := ModuleCat.{z} X)

/-- The global derived-Hom unit evaluated on two strict complexes of `X`-modules. -/
@[stacks 0CS6 "global derived Hom unit component"]
noncomputable abbrev unitApp (M N : CochainComplex (ModuleCat.{z} X) ℤ) :=
  CategoryTheory.CochainComplex.Enriched.RHom.unitApp
    (C := ModuleCat.{z} X) M N

/-- The strict global Hom complex into a K-injective target is canonically the corresponding
global derived-Hom value. -/
@[stacks 070Y "K-injective strict model of global derived Hom"]
noncomputable abbrev unitAppIsoOfKInjective
    (M I : CochainComplex (ModuleCat.{z} X) ℤ) [I.IsKInjective] :=
  CategoryTheory.CochainComplex.Enriched.RHom.unitAppIsoOfKInjective
    (C := ModuleCat.{z} X) M I

/-- A K-injective resolution computes global derived Hom on the standard derived-category
images of its two inputs. -/
@[stacks 0CS6 "K-injective resolution model of global derived Hom"]
noncomputable abbrev resolutionModelIso
    (M : CochainComplex (ModuleCat.{z} X) ℤ)
    {N : CochainComplex (ModuleCat.{z} X) ℤ}
    (I : CochainComplex.KInjectiveResolution N) :=
  CategoryTheory.CochainComplex.Enriched.RHom.resolutionModelIso
    (C := ModuleCat.{z} X) M I

section MaxPresentation

variable {C : Type u} [Category.{v} C]

/-- The max-universe global derived-Hom bifunctor for a commutative ring-sheaf presentation. -/
@[stacks 0CS6 "max-universe global derived Hom"]
noncomputable abbrev maxFunctor (J : GrothendieckTopology C)
    (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  letI := CategoryTheory.CochainComplex.Enriched.RHom.hasRightDerivedFunctor
    (C := ModuleCat.{max u v} (RingedSite.ofCommSheafMax J 𝒪))
  functor.{max u v} (RingedSite.ofCommSheafMax J 𝒪)

/-- The global derived-Hom unit for a max-universe commutative ring-sheaf presentation. -/
@[stacks 0CS6 "max-universe global derived Hom unit"]
noncomputable abbrev maxUnit (J : GrothendieckTopology C)
    (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  letI := CategoryTheory.CochainComplex.Enriched.RHom.hasRightDerivedFunctor
    (C := ModuleCat.{max u v} (RingedSite.ofCommSheafMax J 𝒪))
  unit.{max u v} (RingedSite.ofCommSheafMax J 𝒪)

/-- A K-injective resolution computes global derived Hom for a max-universe commutative
ring-sheaf presentation. -/
@[stacks 0CS6 "max-universe K-injective model of global derived Hom"]
noncomputable abbrev maxResolutionModelIso
    (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{max u v})
    (M : CochainComplex (RingedSite.ModuleCat.{max u v}
      (RingedSite.ofCommSheafMax J 𝒪)) ℤ)
    {N : CochainComplex (RingedSite.ModuleCat.{max u v}
      (RingedSite.ofCommSheafMax J 𝒪)) ℤ}
    (I : CochainComplex.KInjectiveResolution N) :=
  letI := CategoryTheory.CochainComplex.Enriched.RHom.hasRightDerivedFunctor
    (C := ModuleCat.{max u v} (RingedSite.ofCommSheafMax J 𝒪))
  resolutionModelIso.{max u v} (RingedSite.ofCommSheafMax J 𝒪) M I

end MaxPresentation

end RingedSite.Hom.ModuleDerived.RHom
