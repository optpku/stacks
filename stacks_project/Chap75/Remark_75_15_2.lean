module

public import stacks_project.Chap75.Remark_75_15_2_Cohomology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Remark 75.15.2: the supported retract extension of Lemma 75.15.1 can be chosen
so that the retract inclusion `P ⟶ R|_W` induces cohomology-sheaf isomorphisms
in every degree strictly above any prescribed cutoff. The source's finite
shift-biproduct form `R|_W = P ⊕ ⨁ j, P^{⊕ n_j}⟦j⟧` is the proof's intermediate
presentation of this strengthening. -/
@[stacks 09IW]
#check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.exists_supported_retract_extension_isIso_above :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (W : OpenSubspace X) [IsQuasiCompact W.X]
      (T : Closeds (Points X)) (hT : QuasiCompact (OpenSubspace.ofOpensι T.compl))
      (E : DerivedQCoh X) (P : ModuleDerived W.X)
      (hP : ModuleDerived.IsPerfect P)
      (hP_support :
        ModuleDerived.IsSupportedOn P (Points.map W.ι ⁻¹' (T : Set (Points X))))
      (α : P ⟶ (ModuleDerived.pullback W.ι).obj E.obj) (a : ℤ),
      ∃ (R : ModuleDerived X) (hR : ModuleDerived.IsPerfect R)
        (hR_support : ModuleDerived.IsSupportedOn R (T : Set (Points X)))
        (β : R ⟶ E.obj) (r : Retract P ((ModuleDerived.pullback W.ι).obj R)),
        r.i ≫ (ModuleDerived.pullback W.ι).map β = α ∧
          ∀ i : ℤ, a < i →
            IsIso ((DerivedCategory.homologyFunctor (Modules W.X) i).map r.i))
