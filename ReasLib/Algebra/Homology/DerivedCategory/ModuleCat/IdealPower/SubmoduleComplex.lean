module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
public import ReasLib.Algebra.Module.IdealPower.Submodule.Tensor
public import ReasLib.Algebra.Module.IdealPower.Submodule.Sequential
public import ReasLib.CategoryTheory.Pro.Sequential.Isomorphism
public import ReasLib.CategoryTheory.Homology.DoubleComplex.TotalComparison
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived tensor and ideal-power subcomplex systems

For a cochain complex `M` over a commutative ring `A`, this leaf owns the canonical
comparison

`(I ^ (n + 1))[0] ⊗ᴸ[A] M ⟶ I ^ (n + 1) M`.

The stage index is zero-based, so stage `n` uses the positive exponent `n + 1`.
The ordinary chain map is concrete: the only nonzero summand of the degree-zero
single complex is sent to the termwise ideal-power submodule by
`Ideal.PowerSubmodule.tensorMap`.

@stack 0G3N
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory
open CategoryTheory.MonoidalCategory
open ComplexShape
open Opposite

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IdealPower.SubmoduleComplex

variable {A : Type u} [CommRing A]

/- The zero-based positive-exponent indexing is isolated in its own namespace so that the short
names `stage`, `step`, and `system` cannot be confused with the unshifted module stages. -/
namespace Positive

/-- The functor applying the positive adic stage `I ^ (n + 1)` termwise to cochain
complexes. -/
@[stacks 0G3N "positive ideal-power subcomplex functor"]
noncomputable abbrev complexFunctor (I : Ideal A) (n : ℕ) :
    CochainComplex (ModuleCat A) ℤ ⥤ CochainComplex (ModuleCat A) ℤ :=
  (Ideal.PowerSubmodule.functor I (n + 1)).mapHomologicalComplex (up ℤ)

/-- The positive ideal-power subcomplex `I ^ (n + 1) M`. -/
@[stacks 0G3N "positive ideal-power subcomplex"]
abbrev complex (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) :
    CochainComplex (ModuleCat A) ℤ :=
  (complexFunctor I n).obj M

/-- The natural transition from exponent `n + 2` to exponent `n + 1` on adic
subcomplexes. -/
@[stacks 0G3N "positive ideal-power subcomplex transition"]
noncomputable abbrev complexStepNatTrans (I : Ideal A) (n : ℕ) :
    complexFunctor I (n + 1) ⟶ complexFunctor I n :=
  NatTrans.mapHomologicalComplex
    (Ideal.PowerSubmodule.inclusionNatTrans I (Nat.le_succ (n + 1))) (up ℤ)

/-- The transition `I ^ (n + 2) M ⟶ I ^ (n + 1) M`. -/
@[stacks 0G3N "positive ideal-power subcomplex stage transition"]
noncomputable abbrev complexStep
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) :
    complex I M (n + 1) ⟶ complex I M n :=
  (complexStepNatTrans I n).app M

/-- The derived-category stage represented by `I ^ (n + 1) M`. -/
@[stacks 0G3N "positive ideal-power subcomplex derived stage"]
abbrev stage (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) :
    DerivedCategory (ModuleCat A) :=
  DerivedCategory.Q.obj (complex I M n)

/-- The derived transition represented by the inclusion of consecutive adic
subcomplexes. -/
@[stacks 0G3N "positive ideal-power subcomplex derived transition"]
noncomputable abbrev step
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) :
    stage I M (n + 1) ⟶ stage I M n :=
  DerivedCategory.Q.map (complexStep I M n)

/-- The sequential inverse system of positive ideal-power subcomplexes. -/
@[stacks 0G3N "positive ideal-power subcomplex derived system"]
noncomputable abbrev system
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) :
    SequentialInverseSystem (DerivedCategory (ModuleCat A)) :=
  Functor.ofOpSequence (X := fun n ↦ stage I M n) (step I M)

/-- The degree-zero cochain complex on the regular-module stage `I ^ (n + 1)`. -/
@[stacks 0G3N "positive ideal-power regular single complex"]
abbrev singleStage (I : Ideal A) (n : ℕ) : CochainComplex (ModuleCat A) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj
    (Ideal.PowerSubmodule.positiveStageObj I (ModuleCat.of A A) n)

/-- The cochain map between consecutive degree-zero regular ideal-power stages. -/
@[stacks 0G3N "positive ideal-power regular single-complex transition"]
noncomputable abbrev singleStep (I : Ideal A) (n : ℕ) :
    singleStage I (n + 1) ⟶ singleStage I n :=
  (CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).map
    (Ideal.PowerSubmodule.positiveStep I (ModuleCat.of A A) n)

/-- The standard derived tensor stage `(I ^ (n + 1))[0] ⊗ᴸ[A] M`. -/
@[stacks 0G3N "positive ideal-power standard derived tensor stage"]
noncomputable abbrev standardStage
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) :
    DerivedCategory (ModuleCat A) :=
  (DerivedTensor.Bifunctor.rightFunctor (DerivedCategory.Q.obj M)).obj
    (DerivedCategory.Q.obj (singleStage I n))

/-- The standard derived tensor transition induced by the regular ideal-power
inclusion. -/
@[stacks 0G3N "positive ideal-power standard derived tensor transition"]
noncomputable def standardStep
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) :
    standardStage I M (n + 1) ⟶ standardStage I M n :=
  (DerivedTensor.Bifunctor.rightFunctor (DerivedCategory.Q.obj M)).map
    (DerivedCategory.Q.map (singleStep I n))

/-- The standard sequential system `((I ^ (n + 1))[0] ⊗ᴸ[A] M)ₙ`. -/
@[stacks 0G3N "positive ideal-power standard derived tensor system"]
noncomputable def standardSystem
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) :
    SequentialInverseSystem (DerivedCategory (ModuleCat A)) :=
  Functor.ofOpSequence (X := fun n ↦ standardStage I M n) (standardStep I M)

/-- The multiplication map on the unique surviving degree-zero tensor summand. -/
@[stacks 0G3N "ideal-power tensor surviving summand map"]
noncomputable def termMap
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) (i : ℤ) :
    ((curriedTensor (ModuleCat A)).obj ((singleStage I n).X 0)).obj (M.X i) ⟶
      (complex I M n).X i :=
  ((HomologicalComplex.singleObjXSelf (up ℤ) (0 : ℤ)
      (Ideal.PowerSubmodule.positiveStageObj I (ModuleCat.of A A) n)).hom ⊗ₘ
        𝟙 (M.X i)) ≫
    Ideal.PowerSubmodule.tensorMap I (n + 1) (M.X i)

/-- The surviving summand map transported along equality of the module degree. -/
@[stacks 0G3N "transported ideal-power tensor summand map"]
noncomputable def zeroSummandMap
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ)
    {q i : ℤ} (hqi : q = i) :
    ((curriedTensor (ModuleCat A)).obj ((singleStage I n).X 0)).obj (M.X q) ⟶
      (complex I M n).X i :=
  eqToHom
      (congrArg
        (fun k ↦ ((curriedTensor (ModuleCat A)).obj ((singleStage I n).X 0)).obj (M.X k))
        hqi) ≫
    termMap I M n i

/-- The summand map defining ordinary tensor multiplication; all summands away from
degree zero in the single complex are zero. -/
@[stacks 0G3N "ideal-power tensor summand map"]
noncomputable def summandMap
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) (i p q : ℤ)
    (h : (up ℤ).π (up ℤ) (up ℤ) (p, q) = i) :
    ((curriedTensor (ModuleCat A)).obj ((singleStage I n).X p)).obj (M.X q) ⟶
      (complex I M n).X i :=
  dite (p = 0)
    (fun hp ↦
      eqToHom
          (congrArg
            (fun k ↦ ((curriedTensor (ModuleCat A)).obj ((singleStage I n).X k)).obj (M.X q))
            hp) ≫
        zeroSummandMap I M n
          (HomologicalComplex₂.ZeroColumn.index_eq hp h))
    (fun _ ↦ 0)

/-- The degreewise component of ordinary tensor multiplication into the adic
subcomplex. -/
@[stacks 0G3N "ideal-power tensor-complex component"]
noncomputable def tensorComponent
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) (i : ℤ) :
    (HomologicalComplex.tensorObj (singleStage I n) M).X i ⟶
      (complex I M n).X i :=
  HomologicalComplex.mapBifunctorDesc
    (K₁ := singleStage I n) (K₂ := M)
    (F := curriedTensor (ModuleCat A)) (c := up ℤ)
    (A := (complex I M n).X i) (j := i) (summandMap I M n i)

/-- The degreewise tensor multiplication components commute with the cochain
differential. -/
@[stacks 0G3N "differential compatibility of ideal-power tensor multiplication"]
theorem tensorComponent_comm
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ)
    (i j : ℤ) (hij : (up ℤ).Rel i j) :
    tensorComponent I M n i ≫ (complex I M n).d i j =
      (HomologicalComplex.tensorObj (singleStage I n) M).d i j ≫
        tensorComponent I M n j := sorry

/-- The concrete chain map from ordinary tensor totalization to the ideal-power
subcomplex. -/
@[stacks 0G3N "ordinary tensor comparison with ideal-power subcomplex"]
noncomputable def tensorMap
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) :
    HomologicalComplex.tensorObj (singleStage I n) M ⟶ complex I M n where
  f i := tensorComponent I M n i
  comm' i j hij := tensorComponent_comm I M n i j hij

/-- The degree-`i` component of `tensorMap` is `tensorComponent`. -/
@[simp, stacks 0G3N "component formula for ideal-power tensor comparison"]
theorem tensorMap_f
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) (i : ℤ) :
    (tensorMap I M n).f i = tensorComponent I M n i := sorry

/-- The canonical stage comparison from derived tensor to the ideal-power
subcomplex. -/
@[stacks 0G3N "derived tensor comparison with ideal-power subcomplex"]
noncomputable def comparisonApp
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) :
    standardStage I M n ⟶ stage I M n :=
  DerivedTensor.Bifunctor.counitAppOfQ (singleStage I n) M ≫
    DerivedCategory.Q.map (tensorMap I M n)

/-- Consecutive stage comparisons commute with the explicit ideal-power
transitions. -/
@[stacks 0G3N "transition compatibility of ideal-power derived tensor comparison"]
theorem comparisonApp_step
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) :
    standardStep I M n ≫ comparisonApp I M n =
      comparisonApp I M (n + 1) ≫ step I M n := sorry

/-- The stage comparisons are natural for the two sequential inverse systems. -/
@[stacks 0G3N "naturality of ideal-power derived tensor comparison"]
theorem comparisonApp_naturality
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) :
    (standardSystem I M).stepMap n ≫ comparisonApp I M n =
      comparisonApp I M (n + 1) ≫ (system I M).stepMap n := sorry

/-- The derived tensor comparisons assembled into a natural transformation of
sequential inverse systems. -/
@[stacks 0G3N "ideal-power derived tensor comparison natural transformation"]
noncomputable def comparisonNatTrans
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) :
    standardSystem I M ⟶ system I M :=
  NatTrans.ofOpSequence (comparisonApp I M) (comparisonApp_naturality I M)

/-- The sequential pro-morphism represented by the canonical stage comparisons. -/
@[stacks 0G3N "ideal-power derived tensor sequential pro-morphism"]
noncomputable def comparison
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) :
    Pro.SequentialHom (standardSystem I M) (system I M) :=
  Pro.SequentialHom.ofNatTrans (comparisonNatTrans I M)

/-- Lemma 15.102.6: for a bounded complex of finite modules over a Noetherian ring,
the canonical derived tensor comparison with its positive ideal-power subcomplexes
is an isomorphism of pro-objects. -/
@[stacks 0G3N "Lemma 15.102.6"]
theorem comparison_isIso [IsNoetherianRing A]
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ)
    (hboundedBelow : ∃ a : ℤ, M.IsStrictlyGE a)
    (hboundedAbove : ∃ b : ℤ, M.IsStrictlyLE b)
    (hfinite : ∀ i : ℤ, Module.Finite A (M.X i)) :
    IsIso (comparison I M).toHom := sorry

/-- The object formula for the ideal-power subcomplex system. -/
@[simp, stacks 0G3N "object formula for ideal-power subcomplex system"]
theorem system_obj
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) :
    (system I M).obj (op n) = stage I M n := sorry

/-- The transition formula for the ideal-power subcomplex system. -/
@[simp, stacks 0G3N "transition formula for ideal-power subcomplex system"]
theorem system_stepMap
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) :
    (system I M).stepMap n = step I M n := sorry

/-- The object formula for the standard derived tensor system. -/
@[simp, stacks 0G3N "object formula for ideal-power standard tensor system"]
theorem standardSystem_obj
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) :
    (standardSystem I M).obj (op n) = standardStage I M n := sorry

/-- The transition formula for the standard derived tensor system. -/
@[simp, stacks 0G3N "transition formula for ideal-power standard tensor system"]
theorem standardSystem_stepMap
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) :
    (standardSystem I M).stepMap n = standardStep I M n := sorry

/-- The component formula for the comparison natural transformation. -/
@[simp, stacks 0G3N "component formula for ideal-power derived tensor comparison"]
theorem comparisonNatTrans_app
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) :
    (comparisonNatTrans I M).app (op n) = comparisonApp I M n := sorry

/-- The canonical comparison representative uses identity reindexing. -/
@[simp, stacks 0G3N "identity reindexing of ideal-power derived tensor comparison"]
theorem comparison_reindex
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) :
    (comparison I M).reindex = OrderHom.id := sorry

/-- The level map of the canonical comparison representative is `comparisonApp`. -/
@[simp, stacks 0G3N "level map of ideal-power derived tensor comparison"]
theorem comparison_hom_app
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) :
    (comparison I M).hom.app (op n) = comparisonApp I M n := sorry

end Positive

end CategoryTheory.DerivedCategory.IdealPower.SubmoduleComplex
