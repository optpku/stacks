/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent.Relative.Algebraization
import StacksCheckRecall

/-!
# Proposed relative pseudo-coherent generalization of derived Grothendieck existence

Remark 77.13.7 proposes that algebraization should continue to hold when
`X ⟶ Spec A` is separated and of finite presentation, with each stage complex
relatively pseudo-coherent and supported on a closed subset proper over its stage
ring. The source leaves this generalization unproved.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/- Remark 77.13.7 proposes the following relative pseudo-coherent proper-support
algebraization statement; it remains unproved. -/
@[stacks 0DIR] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.exists_pseudoCoherentOver_withProperSupport_of_thickenings :
    ∀ (A : SequentialInverseSystem CommRingCat.{u}) (A_lim : LimitCone A)
    (h_surjective : A.Surjective) (h_kernel : A.KernelLocallyNilpotent)
    (X : AlgebraicSpace (Spec A_lim.cone.pt))

    [Separated (SchemeRealization.toBase X)] [FinitePresentation (SchemeRealization.toBase X)]
    (Xn : ℕ → AlgebraicSpace (Spec A_lim.cone.pt))
    (p : ∀ n, Xn n ⟶ X) (q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n)
    [∀ sq : EtaleSquare (SchemeRealization.toBase X),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [∀ n : ℕ, ∀ sq : EtaleSquare (q n),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    (h_pullback : ∀ n,
      IsPullback (q n) (p n) (Modules.stageSpecToBase A_lim n) (SchemeRealization.toBase X))
    [∀ n, IsClosedImmersion (p n)] [∀ n, LocallyOfFiniteType (q n)]
    (i : ∀ n, Xn n ⟶ Xn (n + 1))
    (hiX : ∀ n, i n ≫ p (n + 1) = p n)
    (hiA : ∀ n, i n ≫ q (n + 1) = q n ≫ Modules.stageSpecTransition A_lim n)
    (Kn : ∀ n, ModuleDerived (Xn n))
    (h_qcoh : ∀ n, derivedQuasiCoherentModuleProperty (Xn n) (Kn n))
    (h_pseudoCoherent : ∀ n, IsPseudoCoherentOver (q n) (Kn n))
    (h_support : ∀ n, ∃ Z : Closeds (Points (Xn n)),
      ClosedSubset.ProperOver (q n) Z ∧
        IsSupportedOn (Kn n) (Z : Set (Points (Xn n))))
    (φ : ∀ n, (pullback (i n)).obj (Kn (n + 1)) ≅ Kn n),
    ∃ (K : ModuleDerived X) (e : ∀ n, (pullback (p n)).obj K ≅ Kn n),
      derivedQuasiCoherentModuleProperty X K ∧
        IsPseudoCoherentOver (SchemeRealization.toBase X) K ∧
          (∃ Z : Closeds (Points X),
            ClosedSubset.ProperOver (SchemeRealization.toBase X) Z ∧
              IsSupportedOn K (Z : Set (Points X))) ∧
            ∀ n, (pullback (i n)).map (e (n + 1)).hom ≫ (φ n).hom =
              (pullbackCompComparison (i n) (p (n + 1))).app K ≫
                eqToHom (congrArg (fun g ↦ (pullback g).obj K) (hiX n)) ≫
                  (e n).hom)

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
