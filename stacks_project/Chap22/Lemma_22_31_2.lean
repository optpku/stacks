/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Subset.Right
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.InternalHom.Derived
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

variable {D : Type u₁} {D' : Type u₂}
variable [Category.{v₁} D] [Category.{v₂} D']
variable (F : D ⥤ D') (S : MorphismProperty D)
variable [S.IsSaturatedMultiplicativeSystem]
variable (I : ObjectProperty D)
variable (hI_reaches : ∀ X : D, ∃ (X' : D) (s : X ⟶ X'), I X' ∧ S s)
variable (hI_isIso :
  ∀ {X X' : D} (s : X ⟶ X'), I X → I X' → S s → IsIso (F.map s))

/- Source-semantic companion: the internal-Hom functor has a total right-derived functor when
every object admits a denominator into a good object and internal denominators between good
objects are inverted. The reusable statement applies to an arbitrary functor and saturated
multiplicative system. -/
#check
  (CategoryTheory.Functor.RightDerived.EverywhereDefined.hasFunctor_of_subset
      F S I hI_reaches hI_isIso :
    F.HasRightDerivedFunctor S)

/- The stronger reusable owner records source-definedness, including essential constancy of each
localization-indexed diagram. -/
#check @CategoryTheory.Functor.RightDerived.EverywhereDefined.of_subset

/- Pointwise existence remains available as a weaker bridge to mathlib's derived-functor API. -/
#check @CategoryTheory.Functor.RightDerived.EverywhereDefined.hasPointwise_of_subset

/- Once installed at a concrete use site, the canonical total right-derived functor is available
without any DG-specific wrapper. -/
#check @CategoryTheory.Functor.totalRightDerived

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {A B : CochainDGAlgebra.{u, v} R}
variable (T : DifferentialGradedBimodule A B)

/- Lemma 22.31.2 (09LI): Property-(I) resolutions canonically supply the concrete Chapter 22
functor's precise derivability condition. -/
@[stacks 09LI]
#check (inferInstance : DifferentialGradedBimodule.InternalHom.HasDerivedFunctor T)

/- The actual derived internal-Hom functor and its canonical unit are available without
rebuilding the generic setup or installing a local instance. -/
#check DifferentialGradedBimodule.InternalHom.derivedFunctor T
#check DifferentialGradedBimodule.InternalHom.derivedUnit T
#check (inferInstance :
  (DifferentialGradedBimodule.InternalHom.derivedFunctor T).IsRightDerivedFunctor
    (DifferentialGradedBimodule.InternalHom.derivedUnit T)
    (DifferentialGradedModule.quasiIso B))
