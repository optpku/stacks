/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap35.Lemma_35_10_4
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Counterexample
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.AssociatedModule

/- Example 35.10.5 (1): on every standard big site over `Spec ℤ`, the associated
module `Coker(2 : 𝒪 ⟶ 𝒪)` is finitely presented. -/
@[stacks 0GND] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.twoCokernelBigIsFinitePresentation :
    ∀ τ : StandardTopology,
      ((bigModuleFunctor (Spec (CommRingCat.of ℤ)) τ).obj
        twoCokernelModule).IsFinitePresentation)

/- Example 35.10.5 (2): the internal Hom from the associated module
`Coker(2 : 𝒪 ⟶ 𝒪)` to the associated structure module maps canonically to
the two-torsion object. -/
@[stacks 0GND] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.twoCokernelInternalHomToTwoTorsionIsIso :
    ∀ τ : StandardTopology,
      IsIso (twoCokernelInternalHomToTwoTorsion τ))

/- Example 35.10.5 (3): the two-torsion in the associated structure module
on every standard big site over `Spec ℤ` is not quasicoherent. -/
@[stacks 0GND] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.bigStructureModuleTwoTorsionNotQuasicoherent :
    ∀ τ : StandardTopology,
      ¬ (bigStructureModuleTwoTorsion τ).IsQuasicoherent)

/- Example 35.10.5 (4): the internal Hom from the associated module
`Coker(2 : 𝒪 ⟶ 𝒪)` to the associated structure module is not quasicoherent. -/
@[stacks 0GND] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.twoCokernelInternalHomNotQuasicoherent :
    ∀ τ : StandardTopology,
      ¬ ((ihom ((bigModuleLift (Spec (CommRingCat.of ℤ)) τ).obj
          ((bigModuleFunctor (Spec (CommRingCat.of ℤ)) τ).obj
            twoCokernelModule))).obj
        ((bigModuleLift (Spec (CommRingCat.of ℤ)) τ).obj
          ((bigModuleFunctor (Spec (CommRingCat.of ℤ)) τ).obj
            (structureModule (Spec (CommRingCat.of ℤ)))))).IsQuasicoherent)

end AlgebraicGeometry.Scheme.AssociatedModule
