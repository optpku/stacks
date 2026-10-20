/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Restriction.Left
public import ReasLib.Algebra.Homology.CochainDGAlgebra.TensorProduct
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Regular
public import ReasLib.RingTheory.Sequence.Koszul.Power
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived factorization for exact-power Koszul complexes

This leaf packages the objects and maps in the factorization of a powered Koszul transition
through `K_n ⊗[R] K_t`.  Exact-power Koszul chain algebras are first embedded into integer-graded
cochain DGAs.  All left module structures are then obtained by restriction of scalars along named
DGA homomorphisms, and passage to the derived category uses the canonical left-module functor.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open scoped TensorProduct

namespace KoszulComplex.Derived

variable {R : Type u} [CommRing R]

/-- The cochain DGA obtained from the Koszul algebra on the exact powers `f i ^ n`. -/
@[stacks 0GZ7 "exact-power Koszul cochain DGA"]
noncomputable abbrev powDGA {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    CochainDGAlgebra R :=
  (CochainDGAlgebra.fromChainCommMon R).obj (KoszulComplex.powAlgebra f n)

/-- The cochain complex underlying `powDGA f n` is the exact-power Koszul complex extended by
zero from natural chain degrees to integer cochain degrees. -/
@[simp]
theorem powDGA_toCochainComplex {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    (powDGA f n).toCochainComplex =
      (KoszulComplex.powComplex f n).extend ComplexShape.embeddingDownNat := sorry

/-- The underlying cochain complex of `powDGA f n` is canonically identified with the extension
of the exact-power Koszul chain complex. -/
@[stacks 0GZ7 "underlying complex of an exact-power Koszul cochain DGA"]
noncomputable def powDGAIso {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    (powDGA f n).toCochainComplex ≅
      (KoszulComplex.powComplex f n).extend ComplexShape.embeddingDownNat :=
  eqToIso (powDGA_toCochainComplex f n)

/-- For `n ≤ m`, the exact-power transition as a homomorphism `K_m ⟶ K_n` of cochain DGAs. -/
@[stacks 0GZ7 "exact-power Koszul cochain-DGA transition"]
noncomputable def powDGAHom {ι : Type u} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) :
    powDGA f m ⟶ powDGA f n :=
  (CochainDGAlgebra.fromChainCommMon R).map (KoszulComplex.powAlgebraMap f h)

/-- After the canonical source and target identifications, the cochain map underlying an
exact-power DGA transition is extension by zero of the corresponding Koszul chain map. -/
@[simp, stacks 0GZ7 "underlying map of an exact-power Koszul cochain-DGA transition"]
theorem powDGAHom_toCochainMap {ι : Type u} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) :
    (powDGAHom f h).toCochainMap =
      (powDGAIso f m).hom ≫
        (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat R)).map
          (KoszulComplex.powMap f h) ≫
        (powDGAIso f n).inv := sorry

/-- The exact-power cochain-DGA transition at a reflexive inequality is the identity. -/
@[simp]
theorem powDGAHom_refl {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    powDGAHom f (le_refl n) = 𝟙 (powDGA f n) := sorry

/-- Exact-power cochain-DGA transitions compose according to transitivity. -/
theorem powDGAHom_comp {ι : Type u} [Finite ι] (f : ι → R) {t n N : ℕ}
    (h_tn : t ≤ n) (h_nN : n ≤ N) :
    powDGAHom f h_nN ≫ powDGAHom f h_tn =
      powDGAHom f (h_tn.trans h_nN) := sorry

/-- The ground-ring tensor product DGA `K_n ⊗[R] K_t` in the integer cochain convention. -/
@[stacks 0GZ7 "ground tensor of exact-power Koszul cochain DGAs"]
noncomputable abbrev tensorDGA {ι : Type u} [Finite ι] (f : ι → R) (n t : ℕ) :
    CochainDGAlgebra R :=
  powDGA f n ⊗[R] powDGA f t

/-- The complex underlying `tensorDGA f n t` is the tensor product of the two exact-power
complexes after extension from natural chain degrees. -/
theorem tensorDGA_toCochainComplex {ι : Type u} [Finite ι] (f : ι → R) (n t : ℕ) :
    (tensorDGA f n t).toCochainComplex =
      HomologicalComplex.tensorObj
        ((KoszulComplex.powComplex f n).extend ComplexShape.embeddingDownNat)
        ((KoszulComplex.powComplex f t).extend ComplexShape.embeddingDownNat) := sorry

/-- The canonical monoidal comparison from the cochain model `tensorDGA f n t` to the extension
of the original ground-ring tensor product of exact-power Koszul chain complexes. -/
@[stacks 0GZ7 "chain-to-cochain comparison for a powered Koszul ground tensor"]
noncomputable def tensorDGAIso {ι : Type u} [Finite ι] (f : ι → R) (n t : ℕ) :
    (tensorDGA f n t).toCochainComplex ≅
      (HomologicalComplex.tensorObj (KoszulComplex.powComplex f n)
        (KoszulComplex.powComplex f t)).extend ComplexShape.embeddingDownNat :=
  eqToIso (tensorDGA_toCochainComplex f n t) ≪≫
    ComplexShape.embeddingDownNat.extendTensorIso
      (KoszulComplex.powComplex f n) (KoszulComplex.powComplex f t)

/-- The exact-power algebra `K_t` as a left DG `K_n`-module through the transition
`K_n ⟶ K_t`. -/
@[stacks 0GZ7 "powered Koszul algebra as a restricted left DG module"]
noncomputable def stageModule {ι : Type u} [Finite ι] (f : ι → R) {t n : ℕ} (h_tn : t ≤ n) :
    LeftDifferentialGradedModule (powDGA f n) :=
  (powDGAHom f h_tn).restrictLeftModule (powDGA f t).leftRegularModule

/-- The homogeneous terms of the restricted stage module are those of `K_t`. -/
@[simp]
theorem stageModule_X {ι : Type u} [Finite ι] (f : ι → R) {t n : ℕ} (h_tn : t ≤ n)
    (k : ℤ) :
    (stageModule f h_tn).X k = (powDGA f t).X k := sorry

/-- The differential of the restricted stage module is the differential of `K_t`. -/
@[simp]
theorem stageModule_d {ι : Type u} [Finite ι] (f : ι → R) {t n : ℕ} (h_tn : t ≤ n)
    (k : ℤ) :
    (stageModule f h_tn).d k = (powDGA f t).leftRegularModule.d k := sorry

/-- The `K_n`-action on `K_t` is multiplication after applying the exact-power transition. -/
@[simp]
theorem stageModule_smul {ι : Type u} [Finite ι] (f : ι → R) {t n : ℕ} (h_tn : t ≤ n)
    (i p : ℤ) (a : (powDGA f n).X i) (x : (powDGA f t).X p) :
    (stageModule f h_tn).smul i p a x =
      (powDGA f t).mul i p (powDGAHom f h_tn i a) x := sorry

/-- Restricting `stageModule f h_tn` further along `powDGAHom f h_nN` gives the target of the
transition from direct restriction to `powDGA f N`. -/
@[stacks 0GZ7 "iterated restriction of a powered Koszul stage"]
noncomputable def restrictedStageModule {ι : Type u} [Finite ι] (f : ι → R) {t n N : ℕ}
    (h_tn : t ≤ n) (h_nN : n ≤ N) :
    LeftDifferentialGradedModule (powDGA f N) :=
  (powDGAHom f h_nN).restrictLeftModule (stageModule f h_tn)

/-- The iterated restriction of `K_t` retains the homogeneous terms of `K_t`. -/
@[simp]
theorem restrictedStageModule_X {ι : Type u} [Finite ι] (f : ι → R) {t n N : ℕ}
    (h_tn : t ≤ n) (h_nN : n ≤ N) (k : ℤ) :
    (restrictedStageModule f h_tn h_nN).X k = (powDGA f t).X k := sorry

/-- The iterated `K_N`-action on `K_t` applies the transitions through `K_n` before
multiplication. -/
@[simp]
theorem restrictedStageModule_smul {ι : Type u} [Finite ι] (f : ι → R) {t n N : ℕ}
    (h_tn : t ≤ n) (h_nN : n ≤ N)
    (i p : ℤ) (a : (powDGA f N).X i) (x : (powDGA f t).X p) :
    (restrictedStageModule f h_tn h_nN).smul i p a x =
      (powDGA f t).mul i p (powDGAHom f h_tn i (powDGAHom f h_nN i a)) x := sorry

/-- The action homomorphism `K_N ⟶ K_n ⊗[R] K_t`, obtained by transition to `K_n` and
inclusion into the left tensor factor. -/
@[stacks 0GZ7 "left action on a powered Koszul ground tensor"]
noncomputable def tensorActionHom {ι : Type u} [Finite ι] (f : ι → R) (t : ℕ) {n N : ℕ}
    (h_nN : n ≤ N) :
    powDGA f N ⟶ tensorDGA f n t :=
  powDGAHom f h_nN ≫
    CochainDGAlgebra.Tensor.leftFactorHom (powDGA f n) (powDGA f t)

/-- The tensor action homomorphism evaluates by first applying the exact-power transition and
then including the result in the left tensor factor. -/
@[simp]
theorem tensorActionHom_apply {ι : Type u} [Finite ι] (f : ι → R) (t : ℕ) {n N : ℕ}
    (h_nN : n ≤ N) (i : ℤ) (a : (powDGA f N).X i) :
    tensorActionHom f t h_nN i a =
      CochainDGAlgebra.Tensor.leftFactorHom (powDGA f n) (powDGA f t) i
        (powDGAHom f h_nN i a) := sorry

/-- The ground tensor `K_n ⊗[R] K_t` as a left DG `K_N`-module through `tensorActionHom`. -/
@[stacks 0GZ7 "powered Koszul ground tensor as a left DG module"]
noncomputable def tensorModule {ι : Type u} [Finite ι] (f : ι → R) (t : ℕ) {n N : ℕ}
    (h_nN : n ≤ N) :
    LeftDifferentialGradedModule (powDGA f N) :=
  (tensorActionHom f t h_nN).restrictLeftModule
    (tensorDGA f n t).leftRegularModule

/-- The homogeneous terms of the tensor module are those of `K_n ⊗[R] K_t`. -/
@[simp]
theorem tensorModule_X {ι : Type u} [Finite ι] (f : ι → R) (t : ℕ) {n N : ℕ}
    (h_nN : n ≤ N) (k : ℤ) :
    (tensorModule f t h_nN).X k = (tensorDGA f n t).X k := sorry

/-- The `K_N`-action on the tensor module follows `K_N ⟶ K_n` and then the left-factor
inclusion. -/
@[simp]
theorem tensorModule_smul {ι : Type u} [Finite ι] (f : ι → R) (t : ℕ) {n N : ℕ}
    (h_nN : n ≤ N) (i p : ℤ)
    (a : (powDGA f N).X i) (x : (tensorDGA f n t).X p) :
    (tensorModule f t h_nN).smul i p a x =
      (tensorDGA f n t).mul i p (tensorActionHom f t h_nN i a) x := sorry

/-- The transition from direct restriction of `powDGA f t` to the iterated restriction through
`powDGA f n`; its underlying map on `powDGA f t` is the identity. -/
@[stacks 0GZ7 "transition between direct and iterated powered Koszul restrictions"]
noncomputable def transitionHom {ι : Type u} [Finite ι] (f : ι → R) {t n N : ℕ}
    (h_tn : t ≤ n) (h_nN : n ≤ N) :
    stageModule f (h_tn.trans h_nN) ⟶ restrictedStageModule f h_tn h_nN where
  hom _ := LinearMap.id
  comm_d := sorry
  comm_smul := sorry

/-- The transition between the two restriction paths is degreewise the identity linear map. -/
@[simp]
theorem transitionHom_hom {ι : Type u} [Finite ι] (f : ι → R) {t n N : ℕ}
    (h_tn : t ≤ n) (h_nN : n ≤ N) (k : ℤ) :
    (transitionHom f h_tn h_nN).hom k = LinearMap.id := sorry

/-- The transition between the two restriction paths fixes every homogeneous element. -/
@[simp]
theorem transitionHom_apply {ι : Type u} [Finite ι] (f : ι → R) {t n N : ℕ}
    (h_tn : t ≤ n) (h_nN : n ≤ N)
    (k : ℤ) (x : (powDGA f t).X k) :
    (transitionHom f h_tn h_nN).hom k x = x := sorry

/-- The cochain map `K_n ⊗[R] K_t ⟶ K_t`: apply the transition in the first factor and then
multiply in `K_t`. -/
@[stacks 0GZ7 "multiplication map from a powered Koszul ground tensor"]
noncomputable def multiplicationMap {ι : Type u} [Finite ι] (f : ι → R) {t n : ℕ}
    (h_tn : t ≤ n) :
    (tensorDGA f n t).toCochainComplex ⟶ (powDGA f t).toCochainComplex :=
  (CochainDGAlgebra.Hom.tensorProduct (powDGAHom f h_tn)
      (CochainDGAlgebra.Hom.id (powDGA f t))).toCochainMap ≫
    CochainDGAlgebra.Tensor.multiplicationMap (powDGA f t)

/-- The cochain multiplication map is the extension of the original powered Koszul
multiplication comparison, transported through the canonical monoidal identifications. -/
@[stacks 0GZ7 "chain-to-cochain compatibility of powered Koszul multiplication"]
theorem multiplicationMap_eq {ι : Type u} [Finite ι] (f : ι → R) {t n : ℕ}
    (h_tn : t ≤ n) :
    multiplicationMap f h_tn =
      (tensorDGAIso f n t).hom ≫
        (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat R)).map
          (KoszulComplex.powTensorMul f h_tn) ≫
        (powDGAIso f t).inv := sorry

/-- Tensor multiplication is a morphism from the `K_N`-action through `K_n` to the iteratively
restricted copy of `K_t`. -/
@[stacks 0GZ7 "multiplication of powered Koszul left DG modules"]
noncomputable def multiplicationHom {ι : Type u} [Finite ι] (f : ι → R) {t n N : ℕ}
    (h_tn : t ≤ n) (h_nN : n ≤ N) :
    tensorModule f t h_nN ⟶ restrictedStageModule f h_tn h_nN where
  hom k := ((multiplicationMap f h_tn).f k).hom
  comm_d := sorry
  comm_smul := sorry

/-- The degreewise linear map of tensor multiplication is the corresponding component of
`multiplicationMap`. -/
@[simp]
theorem multiplicationHom_hom {ι : Type u} [Finite ι] (f : ι → R) {t n N : ℕ}
    (h_tn : t ≤ n) (h_nN : n ≤ N) (k : ℤ) :
    (multiplicationHom f h_tn h_nN).hom k = ((multiplicationMap f h_tn).f k).hom := sorry

/-- Tensor multiplication evaluates through the explicit cochain multiplication map. -/
@[simp]
theorem multiplicationHom_apply {ι : Type u} [Finite ι] (f : ι → R) {t n N : ℕ}
    (h_tn : t ≤ n) (h_nN : n ≤ N)
    (k : ℤ) (x : (tensorDGA f n t).X k) :
    (multiplicationHom f h_tn h_nN).hom k x = (multiplicationMap f h_tn).f k x := sorry

/-- The derived object represented by `stageModule f h_tn`. -/
@[stacks 0GZ7 "derived powered Koszul stage"]
noncomputable def stage {ι : Type u} [Finite ι] (f : ι → R) {t n : ℕ} (h_tn : t ≤ n) :
    LeftDifferentialGradedModule.Derived.Category (powDGA f n) :=
  (LeftDifferentialGradedModule.toDerived (powDGA f n)).obj (stageModule f h_tn)

/-- The derived object obtained by restricting `stageModule f h_tn` further to `powDGA f N`. -/
@[stacks 0GZ7 "iteratively restricted derived powered Koszul stage"]
noncomputable def restrictedStage {ι : Type u} [Finite ι] (f : ι → R) {t n N : ℕ}
    (h_tn : t ≤ n) (h_nN : n ≤ N) :
    LeftDifferentialGradedModule.Derived.Category (powDGA f N) :=
  (LeftDifferentialGradedModule.toDerived (powDGA f N)).obj
    (restrictedStageModule f h_tn h_nN)

/-- The derived left `K_N`-module represented by `K_n ⊗[R] K_t`. -/
@[stacks 0GZ7 "derived powered Koszul ground tensor"]
noncomputable def tensor {ι : Type u} [Finite ι] (f : ι → R) (t : ℕ) {n N : ℕ}
    (h_nN : n ≤ N) :
    LeftDifferentialGradedModule.Derived.Category (powDGA f N) :=
  (LeftDifferentialGradedModule.toDerived (powDGA f N)).obj (tensorModule f t h_nN)

/-- Passage to the derived category sends the explicit left-module transition to the transition
between the two restriction paths. -/
@[stacks 0GZ7 "derived transition between powered Koszul restrictions"]
noncomputable def transition {ι : Type u} [Finite ι] (f : ι → R) {t n N : ℕ}
    (h_tn : t ≤ n) (h_nN : n ≤ N) :
    stage f (h_tn.trans h_nN) ⟶ restrictedStage f h_tn h_nN :=
  (LeftDifferentialGradedModule.toDerived (powDGA f N)).map
    (transitionHom f h_tn h_nN)

/-- Passage to the derived category sends explicit tensor multiplication to a morphism from the
ground tensor object to the iteratively restricted stage. -/
@[stacks 0GZ7 "derived multiplication of a powered Koszul ground tensor"]
noncomputable def multiplication {ι : Type u} [Finite ι] (f : ι → R) {t n N : ℕ}
    (h_tn : t ≤ n) (h_nN : n ≤ N) :
    tensor f t h_nN ⟶ restrictedStage f h_tn h_nN :=
  (LeftDifferentialGradedModule.toDerived (powDGA f N)).map
    (multiplicationHom f h_tn h_nN)

/-- The derived stage is obtained by applying the canonical left-module-to-derived functor. -/
@[simp]
theorem stage_eq {ι : Type u} [Finite ι] (f : ι → R) {t n : ℕ} (h_tn : t ≤ n) :
    stage f h_tn =
      (LeftDifferentialGradedModule.toDerived (powDGA f n)).obj
        (stageModule f h_tn) := sorry

/-- The iteratively restricted derived stage is the image of its explicit left DG module. -/
@[simp]
theorem restrictedStage_eq {ι : Type u} [Finite ι] (f : ι → R) {t n N : ℕ}
    (h_tn : t ≤ n) (h_nN : n ≤ N) :
    restrictedStage f h_tn h_nN =
      (LeftDifferentialGradedModule.toDerived (powDGA f N)).obj
        (restrictedStageModule f h_tn h_nN) := sorry

/-- The derived tensor is obtained by applying the canonical left-module-to-derived functor. -/
@[simp]
theorem tensor_eq {ι : Type u} [Finite ι] (f : ι → R) (t : ℕ) {n N : ℕ}
    (h_nN : n ≤ N) :
    tensor f t h_nN =
      (LeftDifferentialGradedModule.toDerived (powDGA f N)).obj
        (tensorModule f t h_nN) := sorry

/-- The derived transition is the image of the explicit identity-shaped left-module map. -/
@[simp]
theorem transition_eq {ι : Type u} [Finite ι] (f : ι → R) {t n N : ℕ}
    (h_tn : t ≤ n) (h_nN : n ≤ N) :
    transition f h_tn h_nN =
      (LeftDifferentialGradedModule.toDerived (powDGA f N)).map
        (transitionHom f h_tn h_nN) := sorry

/-- Derived multiplication is the image of the explicit multiplication of left DG modules. -/
@[simp]
theorem multiplication_eq {ι : Type u} [Finite ι] (f : ι → R) {t n N : ℕ}
    (h_tn : t ≤ n) (h_nN : n ≤ N) :
    multiplication f h_tn h_nN =
      (LeftDifferentialGradedModule.toDerived (powDGA f N)).map
        (multiplicationHom f h_tn h_nN) := sorry

set_option maxHeartbeats 800000 in
/-- The data witnessing a factorization of a powered Koszul transition through a later derived
stage. The later exponent, comparison map, and factorization law travel together so downstream
constructions do not repeatedly unpack a nested existential. -/
@[stacks 0GZ7 "data of a derived powered Koszul factorization"]
structure Factorization {ι : Type u} [Finite ι] (f : ι → R) {t n : ℕ}
    (h_tn : t ≤ n) where
  /-- The later exponent used for the factorization. -/
  N : ℕ
  /-- The later exponent is strictly larger than the source exponent. -/
  hN : n < N
  /-- The comparison map from the directly restricted stage to the tensor stage. -/
  lift : stage f (h_tn.trans hN.le) ⟶ tensor f t hN.le
  /-- The comparison map followed by multiplication is the canonical transition. -/
  factor : lift ≫ multiplication f h_tn hN.le = transition f h_tn hN.le

/-- Lemma 23.12.4 (Tag 0GZ7): the derived factorization data exists for every positive exact
exponent `t ≤ n`. -/
@[stacks 0GZ7 "existence of derived powered Koszul factorization data"]
theorem nonemptyFactorization {ι : Type u} [Finite ι] (f : ι → R) {t n : ℕ}
    (h_t : 1 ≤ t) (h_tn : t ≤ n) : Nonempty (Factorization f h_tn) := sorry

/-- Lemma 23.12.4 (Tag 0GZ7): for exact exponents `n ≥ t ≥ 1`, some later `powDGA f N`
admits a derived left-module map from the directly restricted `powDGA f t` to
`tensorDGA f n t` whose composite with multiplication is the transition to iterated restriction. -/
@[stacks 0GZ7 "derived factorization of a powered Koszul transition"]
theorem existsFactorization {ι : Type u} [Finite ι] (f : ι → R) {t n : ℕ}
    (h_t : 1 ≤ t) (h_tn : t ≤ n) :
    ∃ (N : ℕ) (hN : n < N)
      (α : stage f (h_tn.trans hN.le) ⟶ tensor f t hN.le),
      α ≫ multiplication f h_tn hN.le = transition f h_tn hN.le := sorry

end KoszulComplex.Derived
