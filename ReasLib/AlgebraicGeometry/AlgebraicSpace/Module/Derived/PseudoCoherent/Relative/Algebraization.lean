/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FormalSystem
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubset.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RestrictToScheme.LeftDerived

/-!
# Algebraization of relatively pseudo-coherent derived modules with proper support

Compatible relatively pseudo-coherent complexes with proper support over successive
locally nilpotent thickenings algebraize over the inverse limit of the base rings.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- Over a separated algebraic space of finite presentation over an inverse limit of
rings with surjective transition maps and locally nilpotent kernels, a compatible
system of relatively pseudo-coherent complexes with quasi-coherent cohomology and
proper support algebraizes to a relatively pseudo-coherent complex with
quasi-coherent cohomology and proper support, compatibly with the transition maps. -/
theorem exists_pseudoCoherentOver_withProperSupport_of_thickenings
    (A : SequentialInverseSystem CommRingCat.{u}) (A_lim : LimitCone A)
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
    (φ : ∀ n, (pullback (i n)).obj (Kn (n + 1)) ≅ Kn n) :
    ∃ (K : ModuleDerived X) (e : ∀ n, (pullback (p n)).obj K ≅ Kn n),
      derivedQuasiCoherentModuleProperty X K ∧
        IsPseudoCoherentOver (SchemeRealization.toBase X) K ∧
          (∃ Z : Closeds (Points X),
            ClosedSubset.ProperOver (SchemeRealization.toBase X) Z ∧
              IsSupportedOn K (Z : Set (Points X))) ∧
            ∀ n, (pullback (i n)).map (e (n + 1)).hom ≫ (φ n).hom =
              (pullbackCompComparison (i n) (p (n + 1))).app K ≫
                eqToHom (congrArg (fun g ↦ (pullback g).obj K) (hiX n)) ≫
                  (e n).hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
