/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Derived

@[expose] public section

/-!
# Open-cover criteria for pseudo-coherence

This leaf exposes the top-space open-cover formulations used on ringed spaces.  The predicates
remain owned by the generic ringed-site API; these are the construction and elimination views
needed by local arguments.
-/

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

namespace CochainComplex

/-- A complex has a strictly perfect approximation in degree `m` on `U` when its restriction
receives a map from a strictly perfect complex with the required homology behavior. -/
def HasStrictlyPerfectApproximationInDegreeOnOpen
    (E : _root_.CochainComplex (Modules X) ℤ) (U : Opens X.carrier) (m : ℤ) : Prop :=
  ∃ P : _root_.CochainComplex (Modules (X.restrict U.isOpenEmbedding)) ℤ,
    SheafOfModules.CochainComplex.IsStrictlyPerfect P ∧
      ∃ α : P ⟶ (moduleRestrictionComplexToOpen X U).obj E,
        (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
          Epi (HomologicalComplex.homologyMap α m)

/-- Complex `m`-pseudo-coherence is equivalent to admitting strict-perfect approximations on
the members of a top-space open cover. -/
theorem isMPseudoCoherent_iff_exists_openCover
    (E : _root_.CochainComplex (Modules X) ℤ) (m : ℤ) :
    IsMPseudoCoherent E m ↔
      ∃ (I : Type u) (U : I → Opens X.carrier), IsOpenCover U ∧
        ∀ i : I, HasStrictlyPerfectApproximationInDegreeOnOpen E (U i) m := sorry

/-- An open cover carrying strict-perfect approximations exhibits complex
`m`-pseudo-coherence. -/
theorem isMPseudoCoherent_of_isOpenCover
    {I : Type u} {U : I → Opens X.carrier}
    {E : _root_.CochainComplex (Modules X) ℤ} {m : ℤ}
    (hU : IsOpenCover U)
    (hE : ∀ i : I, HasStrictlyPerfectApproximationInDegreeOnOpen E (U i) m) :
    IsMPseudoCoherent E m := sorry

/-- A complex that is `m`-pseudo-coherent admits a witnessing top-space open cover. -/
theorem IsMPseudoCoherent.exists_openCover
    {E : _root_.CochainComplex (Modules X) ℤ} {m : ℤ} (hE : IsMPseudoCoherent E m) :
    ∃ (I : Type u) (U : I → Opens X.carrier), IsOpenCover U ∧
      ∀ i : I, HasStrictlyPerfectApproximationInDegreeOnOpen E (U i) m := sorry

end CochainComplex

namespace ModuleDerived

/-- A derived module has a strictly perfect approximation in degree `m` on `U` when its
restriction receives a morphism from the derived image of a strictly perfect complex. -/
def HasStrictlyPerfectApproximationInDegreeOnOpen
    (K : ModuleDerived X) (U : Opens X.carrier) (m : ℤ) : Prop :=
  ∃ P : _root_.CochainComplex (Modules (X.restrict U.isOpenEmbedding)) ℤ,
    SheafOfModules.CochainComplex.IsStrictlyPerfect P ∧
      ∃ α : DerivedCategory.Q.obj P ⟶ (moduleRestrictionToOpenDerived X U).obj K,
        (∀ j : ℤ, m < j →
          IsIso ((DerivedCategory.homologyFunctor (Modules (X.restrict U.isOpenEmbedding)) j).map α)) ∧
          Epi ((DerivedCategory.homologyFunctor
            (Modules (X.restrict U.isOpenEmbedding)) m).map α)

/-- Derived `m`-pseudo-coherence is equivalent to admitting strict-perfect approximations on
the members of a top-space open cover. -/
theorem isMPseudoCoherent_iff_exists_openCover (K : ModuleDerived X) (m : ℤ) :
    IsMPseudoCoherent K m ↔
      ∃ (I : Type u) (U : I → Opens X.carrier), IsOpenCover U ∧
        ∀ i : I, HasStrictlyPerfectApproximationInDegreeOnOpen K (U i) m := sorry

/-- An open cover carrying strict-perfect approximations exhibits derived
`m`-pseudo-coherence. -/
theorem isMPseudoCoherent_of_isOpenCover
    {I : Type u} {U : I → Opens X.carrier} {K : ModuleDerived X} {m : ℤ}
    (hU : IsOpenCover U)
    (hK : ∀ i : I, HasStrictlyPerfectApproximationInDegreeOnOpen K (U i) m) :
    IsMPseudoCoherent K m := sorry

/-- A derived module that is `m`-pseudo-coherent admits a witnessing top-space open cover. -/
theorem IsMPseudoCoherent.exists_openCover
    {K : ModuleDerived X} {m : ℤ} (hK : IsMPseudoCoherent K m) :
    ∃ (I : Type u) (U : I → Opens X.carrier), IsOpenCover U ∧
      ∀ i : I, HasStrictlyPerfectApproximationInDegreeOnOpen K (U i) m := sorry

end ModuleDerived

end AlgebraicGeometry.RingedSpace
