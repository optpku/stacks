module

public import stacks_project.Chap67.Lemma_67_28_5
public import stacks_project.Chap75.Definition_75_3_2_SupportedOn
public import stacks_project.Chap75.Lemma_75_7_3_ProperOver
public import stacks_project.Chap75.Lemma_75_26_6_Pullback
public import stacks_project.Chap76.Lemma_76_45_4_Relative
public import stacks_project.Chap77.Situation_77_12_1_FormalSystem

/-!
# Derived Grothendieck existence in the relatively pseudo-coherent proper-support generality

Remark 77.13.7 records that the algebraization in this section should continue to
hold when `X ⟶ Spec A` is only separated and of finite presentation, with each
stage complex relatively pseudo-coherent and supported on a closed subset proper
over the corresponding stage ring.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- Remark 77.13.7: if `X ⟶ Spec A` is separated and of finite presentation, and
each `K n` is pseudo-coherent relative to `A n` and supported on a closed subset
of `X n` proper over `A n`, then the system algebraizes to a `K` which is
pseudo-coherent relative to `A` and supported on a closed subset proper over `A`. -/
@[stacks 0DIR]
theorem exists_pseudoCoherentOver_withProperSupport_of_thickenings
    (A : SequentialInverseSystem CommRingCat.{u}) (A_lim : LimitCone A)
    (h_surjective : A.Surjective) (h_kernel : A.KernelLocallyNilpotent)
    (X : AlgebraicSpace (Spec A_lim.cone.pt))
    [Separated (toBase X)] [FinitePresentation (toBase X)]
    (Xn : ℕ → AlgebraicSpace (Spec A_lim.cone.pt))
    (p : ∀ n, Xn n ⟶ X) (q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n)
    (h_pullback : ∀ n,
      IsPullback (q n) (p n) (Modules.stageSpecToBase A_lim n) (toBase X))
    [∀ n, IsClosedImmersion (p n)] [∀ n, LocallyOfFiniteType (q n)]
    (i : ∀ n, Xn n ⟶ Xn (n + 1))
    (hiX : ∀ n, i n ≫ p (n + 1) = p n)
    (hiA : ∀ n, i n ≫ q (n + 1) = q n ≫ Modules.stageSpecTransition A_lim n)
    (Kn : ∀ n, ModuleDerived (Xn n))
    (h_qcoh : ∀ n, derivedQuasiCoherentModuleProperty (Xn n) (Kn n))
    (h_pseudoCoherent : ∀ n, IsPseudoCoherentOver (q n) (Kn n))
    (h_support : ∀ n, ∃ Z : Closeds (Points (Xn n)),
      ClosedSubset.IsProperOver (q n) Z ∧
        IsSupportedOn (Kn n) (Z : Set (Points (Xn n))))
    (φ : ∀ n, (pullback (i n)).obj (Kn (n + 1)) ≅ Kn n) :
    ∃ (K : ModuleDerived X) (e : ∀ n, (pullback (p n)).obj K ≅ Kn n),
      derivedQuasiCoherentModuleProperty X K ∧
        IsPseudoCoherentOver (toBase X) K ∧
          (∃ Z : Closeds (Points X),
            ClosedSubset.IsProperOver (toBase X) Z ∧
              IsSupportedOn K (Z : Set (Points X))) ∧
            ∀ n, (pullback (i n)).map (e (n + 1)).hom ≫ (φ n).hom =
              (pullbackCompComparison (i n) (p (n + 1))).app K ≫
                eqToHom (congrArg (fun g ↦ (pullback g).obj K) (hiX n)) ≫
                  (e n).hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
