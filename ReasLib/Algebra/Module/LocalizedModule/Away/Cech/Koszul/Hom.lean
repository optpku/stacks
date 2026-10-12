/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Iso
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dual.Basis
public import ReasLib.Algebra.Homology.CochainComplex.Truncate.Colimit
public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Koszul
public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Tensor

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape MonoidalCategory Set
open scoped TensorProduct

noncomputable section

universe u

namespace LocalizedModule.Away.Cech

namespace Koszul

open Alternating

variable {A : Type u} [CommRing A] {r : ℕ}

/-- The degree-`p` term of the contragredient powered-Koszul complex with coefficients in `M`. -/
abbrev homTerm (r : ℕ) (M : ModuleCat A) (p : ℕ) : ModuleCat A :=
  ModuleCat.of A ((⋀[A]^(p + 1) (Fin r → A)) →ₗ[A] M)

/-- The contragredient differential is negative precomposition by the powered Koszul
differential. -/
noncomputable def homDifferential (f : Fin r → A) (M : ModuleCat A) (n p : ℕ) :
    ((⋀[A]^(p + 1) (Fin r → A)) →ₗ[A] M) →ₗ[A]
      ((⋀[A]^(p + 2) (Fin r → A)) →ₗ[A] M) :=
  -LinearMap.lcomp A M
    (koszulDifferentialLinearMap (KoszulComplex.powerLinearForm f n) (p + 1))

/-- Evaluating the contragredient differential is negative precomposition by the Koszul
differential. -/
theorem homDifferential_apply (f : Fin r → A) (M : ModuleCat A) (n p : ℕ)
    (g : (⋀[A]^(p + 1) (Fin r → A)) →ₗ[A] M)
    (x : ⋀[A]^(p + 2) (Fin r → A)) :
    homDifferential f M n p g x =
      -g (koszulDifferentialLinearMap (KoszulComplex.powerLinearForm f n) (p + 1) x) := sorry

/-- The differential between arbitrary degrees of the contragredient stage. -/
noncomputable def homDifferentialBetween (f : Fin r → A) (M : ModuleCat A)
    (n p q : ℕ) : homTerm r M p ⟶ homTerm r M q :=
  if h : q = p + 1 then
    ModuleCat.ofHom (homDifferential f M n p) ≫
      eqToHom (congrArg (homTerm r M) h.symm)
  else
    0

/-- The contragredient differential vanishes away from consecutive cochain degrees. -/
theorem homDifferentialBetween_shape (f : Fin r → A) (M : ModuleCat A)
    (n p q : ℕ) (hpq : ¬(up ℕ).Rel p q) :
    homDifferentialBetween f M n p q = 0 := sorry

/-- Consecutive contragredient powered-Koszul differentials compose to zero. -/
theorem homDifferentialBetween_comp (f : Fin r → A) (M : ModuleCat A)
    (n p q s : ℕ) (hpq : (up ℕ).Rel p q) (hqs : (up ℕ).Rel q s) :
    homDifferentialBetween f M n p q ≫ homDifferentialBetween f M n q s = 0 := sorry

/-- The zero-based contragredient Hom complex at exponent `n + 1`. -/
noncomputable def homStage (f : Fin r → A) (M : ModuleCat A) (n : ℕ) :
    CochainComplex (ModuleCat A) ℕ where
  X := homTerm r M
  d := homDifferentialBetween f M n
  shape := homDifferentialBetween_shape f M n
  d_comp_d' := homDifferentialBetween_comp f M n

/-- Degree `p` of `homStage f M n` is `Hom_A(∧^(p+1)(Fin r → A), M)`. -/
theorem homStage_X (f : Fin r → A) (M : ModuleCat A) (n p : ℕ) :
    (homStage f M n).X p = homTerm r M p := sorry

/-- The consecutive differential of `homStage` is the negative contragredient Koszul map. -/
theorem homStage_d (f : Fin r → A) (M : ModuleCat A) (n p : ℕ) :
    (homStage f M n).d p (p + 1) = ModuleCat.ofHom (homDifferential f M n p) := sorry

/-- Precomposition by the adjacent powered-Koszul transition in Hom degree `p`. -/
noncomputable def homStepComponent (f : Fin r → A) (M : ModuleCat A) (n p : ℕ) :
    (homStage f M n).X p ⟶ (homStage f M (n + 1)).X p :=
  ModuleCat.ofHom
    (LinearMap.lcomp A M (KoszulComplex.powerStepComponent f (p + 1)).hom)

/-- A Hom-system transition acts by precomposition with the powered-Koszul transition. -/
theorem homStepComponent_hom (f : Fin r → A) (M : ModuleCat A) (n p : ℕ) :
    (homStepComponent f M n p).hom =
      LinearMap.lcomp A M (KoszulComplex.powerStepComponent f (p + 1)).hom := sorry

/-- Precomposition transitions commute with the contragredient differentials. -/
theorem homStepComponent_comm (f : Fin r → A) (M : ModuleCat A) (n : ℕ)
    {p q : ℕ} (hpq : (up ℕ).Rel p q) :
    homStepComponent f M n p ≫ (homStage f M (n + 1)).d p q =
      (homStage f M n).d p q ≫ homStepComponent f M n q := sorry

/-- The transition from exponent `n + 1` to exponent `n + 2` in the contragredient Hom system. -/
noncomputable def homStep (f : Fin r → A) (M : ModuleCat A) (n : ℕ) :
    homStage f M n ⟶ homStage f M (n + 1) where
  f := homStepComponent f M n
  comm' := fun _ _ hpq ↦ homStepComponent_comm f M n hpq

/-- The zero-based direct system of contragredient powered-Koszul Hom complexes. -/
noncomputable def homSystem (f : Fin r → A) (M : ModuleCat A) :
    ℕ ⥤ CochainComplex (ModuleCat A) ℕ :=
  Functor.ofSequence (homStep f M)

/-- Object `n` of `homSystem f M` is the Hom complex for exponent `n + 1`. -/
theorem homSystem_obj (f : Fin r → A) (M : ModuleCat A) (n : ℕ) :
    (homSystem f M).obj n = homStage f M n := sorry

/-- The sign of the ordered decomposition of `Fin r` into a subset and its complement. -/
noncomputable def complementSign (s : powersetCard (Fin r) p) : Aˣ :=
  (-1 : Aˣ) ^
    (p * (p - 1) / 2 + ∑ i ∈ s.1, (Finset.Iio i \ s.1).card)

/-- Signed complementary subsets identify the complementary exterior power with the dual
exterior power. -/
noncomputable def complementDualEquiv (p : ℕ) (hp : p ≤ r) :
    ⋀[A]^(r - p) (Fin r → A) ≃ₗ[A] Module.Dual A (⋀[A]^p (Fin r → A)) :=
  (exteriorBasis (r - p)).equiv
    ((exteriorBasis p).dualBasis.unitsSMul complementSign)
    (powersetCard.compl ((Nat.add_sub_of_le hp).trans (Fintype.card_fin r).symm))

/-- On an exterior basis vector, `complementDualEquiv` is the signed dual basis vector indexed
by the complementary subset. -/
theorem complementDualEquiv_basis (p : ℕ) (hp : p ≤ r)
    (s : powersetCard (Fin r) (r - p)) :
    (complementDualEquiv p hp :
      ⋀[A]^(r - p) (Fin r → A) ≃ₗ[A] Module.Dual A (⋀[A]^p (Fin r → A)))
        (exteriorBasis (r - p) s) =
      (complementSign
          (powersetCard.compl
            ((Nat.add_sub_of_le hp).trans (Fintype.card_fin r).symm) s) : Aˣ) •
        (exteriorBasis p :
          Module.Basis (powersetCard (Fin r) p) A (⋀[A]^p (Fin r → A))).dualBasis
          (powersetCard.compl
            ((Nat.add_sub_of_le hp).trans (Fintype.card_fin r).symm) s) := sorry

/-- Tensoring the signed complementary-dual equivalence with `M` gives the finite-free
self-duality identification with `Hom_A(∧^p(Fin r → A), M)`. -/
noncomputable def homTensorLinearEquiv (M : ModuleCat A) (p : ℕ) (hp : p ≤ r) :
    M ⊗[A] ⋀[A]^(r - p) (Fin r → A) ≃ₗ[A]
      ((⋀[A]^p (Fin r → A)) →ₗ[A] M) :=
  TensorProduct.comm A M (⋀[A]^(r - p) (Fin r → A)) ≪≫ₗ
    (complementDualEquiv p hp).rTensor M ≪≫ₗ
    dualTensorHomEquivOfBasis (exteriorBasis p)

/-- The finite-free self-duality map is evaluation of the signed complementary dual tensor. -/
theorem homTensorLinearEquiv_apply (M : ModuleCat A) (p : ℕ) (hp : p ≤ r)
    (x : M ⊗[A] ⋀[A]^(r - p) (Fin r → A)) :
    homTensorLinearEquiv M p hp x =
      dualTensorHom A (⋀[A]^p (Fin r → A)) M
        (((complementDualEquiv p hp).rTensor M)
          (TensorProduct.comm A M (⋀[A]^(r - p) (Fin r → A)) x)) := sorry

/-- The truncated tensorized complementary-exterior stage. -/
noncomputable abbrev tensorStage (f : Fin r → A) (M : ModuleCat A) (n : ℕ) :
    CochainComplex (ModuleCat A) ℕ :=
  CochainComplex.truncate.obj ((Alternating.Tensor.complexFunctor M).obj (stage f n))

/-- Degree `p` of `tensorStage` is degree `p + 1` of the tensorized reindexed Koszul stage. -/
theorem tensorStage_X (f : Fin r → A) (M : ModuleCat A) (n p : ℕ) :
    (tensorStage f M n).X p =
      ((Alternating.Tensor.complexFunctor M).obj (stage f n)).X (p + 1) := sorry

/-- The direct system of truncated tensorized complementary-exterior stages. -/
noncomputable abbrev tensorSystem (f : Fin r → A) (M : ModuleCat A) :
    ℕ ⥤ CochainComplex (ModuleCat A) ℕ :=
  system f ⋙ Alternating.Tensor.complexFunctor M ⋙ CochainComplex.truncate

/-- Object `n` of `tensorSystem` is `tensorStage f M n`. -/
theorem tensorSystem_obj (f : Fin r → A) (M : ModuleCat A) (n : ℕ) :
    (tensorSystem f M).obj n = tensorStage f M n := sorry

/-- Above the exterior amplitude, the zero maps give the comparison component because both
modules vanish. -/
theorem zeroComparison_hom_inv_id (f : Fin r → A) (M : ModuleCat A) (n p : ℕ)
    (hp : ¬p + 1 ≤ r) :
    (0 : homTerm r M p ⟶ (tensorStage f M n).X p) ≫
      (0 : (tensorStage f M n).X p ⟶ homTerm r M p) = 𝟙 (homTerm r M p) := sorry

/-- Above the exterior amplitude, the reverse composite of the zero comparison maps is the
identity. -/
theorem zeroComparison_inv_hom_id (f : Fin r → A) (M : ModuleCat A) (n p : ℕ)
    (hp : ¬p + 1 ≤ r) :
    (0 : (tensorStage f M n).X p ⟶ homTerm r M p) ≫
      (0 : homTerm r M p ⟶ (tensorStage f M n).X p) =
        𝟙 ((tensorStage f M n).X p) := sorry

/-- The signed finite-free self-duality isomorphism in degree `p` of a powered stage. -/
noncomputable def homStageComponentIso (f : Fin r → A) (M : ModuleCat A) (n p : ℕ) :
    (homStage f M n).X p ≅ (tensorStage f M n).X p :=
  if hp : p + 1 ≤ r then
    ((tensorLeft (ModuleCat.of A M)).mapIso (stageIso f n (p + 1) hp) ≪≫
      (homTensorLinearEquiv M (p + 1) hp).toModuleIso).symm
  else
    { hom := 0
      inv := 0
      hom_inv_id := zeroComparison_hom_inv_id f M n p hp
      inv_hom_id := zeroComparison_inv_hom_id f M n p hp }

/-- The signed self-duality components commute with the contragredient and tensorized
differentials. -/
theorem homStageComponentIso_comm (f : Fin r → A) (M : ModuleCat A) (n p q : ℕ)
    (hpq : (up ℕ).Rel p q) :
    (homStageComponentIso f M n p).hom ≫ (tensorStage f M n).d p q =
      (homStage f M n).d p q ≫ (homStageComponentIso f M n q).hom := sorry

/-- The contragredient Hom stage is canonically isomorphic to the truncated tensorized
complementary-exterior stage. -/
noncomputable def homStageTensorIso (f : Fin r → A) (M : ModuleCat A) (n : ℕ) :
    homStage f M n ≅ tensorStage f M n :=
  HomologicalComplex.Hom.isoOfComponents (homStageComponentIso f M n)
    (homStageComponentIso_comm f M n)

/-- The component of `homStageTensorIso` is the signed complementary-basis comparison. -/
theorem homStageTensorIso_hom_f (f : Fin r → A) (M : ModuleCat A) (n p : ℕ) :
    (homStageTensorIso f M n).hom.f p = (homStageComponentIso f M n p).hom := sorry

/-- The stagewise Hom-tensor comparisons respect the direct-system transitions. -/
theorem homStageTensorIso_naturality (f : Fin r → A) (M : ModuleCat A) (n : ℕ) :
    (homSystem f M).map (homOfLE (n.le_add_right 1)) ≫
        (homStageTensorIso f M (n + 1)).hom =
      (homStageTensorIso f M n).hom ≫
        (tensorSystem f M).map (homOfLE (n.le_add_right 1)) := sorry

/-- The stagewise Hom-tensor comparison is natural for every morphism of the sequential index
category. -/
theorem homStageTensorIso_naturality_all (f : Fin r → A) (M : ModuleCat A)
    {n m : ℕ} (a : n ⟶ m) :
    (homSystem f M).map a ≫ (homStageTensorIso f M m).hom =
      (homStageTensorIso f M n).hom ≫ (tensorSystem f M).map a := sorry

/-- The stagewise comparisons assemble to a natural isomorphism from the contragredient Hom
system to the truncated tensorized complementary-exterior system. -/
noncomputable def homTensorSystemIso (f : Fin r → A) (M : ModuleCat A) :
  homSystem f M ≅ tensorSystem f M :=
  NatIso.ofComponents (homStageTensorIso f M)
    (homStageTensorIso_naturality_all f M)

/-- The component of `homTensorSystemIso` at exponent `n + 1` is `homStageTensorIso f M n`. -/
theorem homTensorSystemIso_app (f : Fin r → A) (M : ModuleCat A) (n : ℕ) :
    (homTensorSystemIso f M).app n = homStageTensorIso f M n := sorry

/-- The canonical comparison from the tensorized complementary-exterior colimit to the
alternating Cech complex. -/
noncomputable def tensorColimitIso (f : Fin r → A) (M : ModuleCat A) :
    colimit (tensorSystem f M) ≅ Alternating.complex f M :=
  (preservesColimitIso CochainComplex.truncate
      (system f ⋙ Alternating.Tensor.complexFunctor M)).symm ≪≫
    (CochainComplex.truncate.mapIso
      (Alternating.Tensor.extendedIso f M ≪≫
        (Alternating.Tensor.complexFunctor M).mapIso (extendedIso f) ≪≫
        preservesColimitIso (Alternating.Tensor.complexFunctor M) (system f))).symm ≪≫
    CochainComplex.truncateAugment (Alternating.complex f M)
      (Alternating.augmentationMap f M)
      (Alternating.augmentationMap_comp_d_zero_one f M)

/-- The forward map of `tensorColimitIso` is the established tensor-colimit comparison. -/
theorem tensorColimitIso_hom (f : Fin r → A) (M : ModuleCat A) :
    (tensorColimitIso f M).hom =
      (preservesColimitIso CochainComplex.truncate
        (system f ⋙ Alternating.Tensor.complexFunctor M)).inv ≫
        (CochainComplex.truncate.mapIso
          (Alternating.Tensor.extendedIso f M ≪≫
            (Alternating.Tensor.complexFunctor M).mapIso (extendedIso f) ≪≫
            preservesColimitIso (Alternating.Tensor.complexFunctor M) (system f))).inv ≫
        (CochainComplex.truncateAugment (Alternating.complex f M)
          (Alternating.augmentationMap f M)
          (Alternating.augmentationMap_comp_d_zero_one f M)).hom := sorry

/-- The colimit of the contragredient Hom complexes of the powered Koszul complexes is
canonically isomorphic to the alternating Cech complex with the same coefficients. -/
@[stacks 08D0 "canonical Hom-colimit comparison with the alternating Cech complex"]
noncomputable def homColimitIso (f : Fin r → A) (M : ModuleCat A) :
    colimit (homSystem f M) ≅ Alternating.complex f M :=
  HasColimit.isoOfNatIso (homTensorSystemIso f M) ≪≫ tensorColimitIso f M

/-- The forward map of `homColimitIso` first applies signed finite-free self-duality and then the
tensor-colimit Cech comparison. -/
theorem homColimitIso_hom (f : Fin r → A) (M : ModuleCat A) :
    (homColimitIso f M).hom =
      (HasColimit.isoOfNatIso (homTensorSystemIso f M)).hom ≫
        (tensorColimitIso f M).hom := sorry

/-- On the exponent-`n + 1` stage, the forward comparison is the signed Hom-tensor stage map
followed by the tensor-system colimit inclusion and the tensor-colimit Cech comparison. -/
theorem homColimitIso_hom_ι (f : Fin r → A) (M : ModuleCat A) (n : ℕ) :
    colimit.ι (homSystem f M) n ≫ (homColimitIso f M).hom =
      (homStageTensorIso f M n).hom ≫ colimit.ι (tensorSystem f M) n ≫
        (tensorColimitIso f M).hom := sorry

/-- The inverse of `homColimitIso` is the reverse tensor-Cech comparison followed by inverse
finite-free self-duality on the colimit. -/
theorem homColimitIso_inv (f : Fin r → A) (M : ModuleCat A) :
    (homColimitIso f M).inv =
      (tensorColimitIso f M).inv ≫
        (HasColimit.isoOfNatIso (homTensorSystemIso f M)).inv := sorry

/-- Postcomposition by a coefficient morphism in every degree of a contragredient Hom stage. -/
noncomputable def homMapComponent (f : Fin r → A) {M N : ModuleCat A}
    (g : M ⟶ N) (n p : ℕ) : (homStage f M n).X p ⟶ (homStage f N n).X p :=
  ModuleCat.ofHom
    (LinearMap.llcomp A (⋀[A]^(p + 1) (Fin r → A)) M N g.hom)

/-- Coefficient postcomposition commutes with the contragredient differentials. -/
theorem homMapComponent_comm (f : Fin r → A) {M N : ModuleCat A} (g : M ⟶ N)
    (n : ℕ) {p q : ℕ} (hpq : (up ℕ).Rel p q) :
    homMapComponent f g n p ≫ (homStage f N n).d p q =
      (homStage f M n).d p q ≫ homMapComponent f g n q := sorry

/-- A coefficient morphism induces a map of contragredient Hom stages by postcomposition. -/
noncomputable def homMap (f : Fin r → A) {M N : ModuleCat A} (g : M ⟶ N) (n : ℕ) :
    homStage f M n ⟶ homStage f N n where
  f := homMapComponent f g n
  comm' := fun _ _ hpq ↦ homMapComponent_comm f g n hpq

/-- Coefficient postcomposition is compatible with the exponent transitions. -/
theorem homMap_naturality (f : Fin r → A) {M N : ModuleCat A} (g : M ⟶ N) (n : ℕ) :
    (homSystem f M).map (homOfLE (n.le_add_right 1)) ≫ homMap f g (n + 1) =
      homMap f g n ≫ (homSystem f N).map (homOfLE (n.le_add_right 1)) := sorry

/-- Functoriality of the contragredient Hom system in its coefficient module. -/
noncomputable def homSystemMap (f : Fin r → A) {M N : ModuleCat A} (g : M ⟶ N) :
    homSystem f M ⟶ homSystem f N :=
  NatTrans.ofSequence (homMap f g) (homMap_naturality f g)

/-- The component of `homSystemMap` is degreewise postcomposition by the coefficient map. -/
theorem homSystemMap_app (f : Fin r → A) {M N : ModuleCat A} (g : M ⟶ N) (n : ℕ) :
    (homSystemMap f g).app n = homMap f g n := sorry

/-- The canonical Hom-colimit comparison is natural in the coefficient module. -/
theorem homColimitIso_hom_naturality (f : Fin r → A) {M N : ModuleCat A} (g : M ⟶ N) :
    colim.map (homSystemMap f g) ≫ (homColimitIso f N).hom =
      (homColimitIso f M).hom ≫
        (Tensor.complexIso f M).hom ≫
        (NatTrans.mapHomologicalComplex
          ((curriedTensor (ModuleCat A)).map g) (up ℕ)).app (Alternating.complex f A) ≫
        (Tensor.complexIso f N).inv := sorry

end Koszul

end LocalizedModule.Away.Cech

end
