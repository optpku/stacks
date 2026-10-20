/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.EqToHom
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Kernels

/-!
# Finite products, kernels and cokernels of ℤ_[ℓ]-sheaves

Finite products and zero objects of `ℤ_[ℓ]`-sheaves are computed stagewise on the
underlying inverse systems. Kernels and cokernels are the named `ker`/`coker`
constructions, with explicit universal morphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Sheaf CategoryTheory.SequentialInverseSystem
open scoped ZeroObject

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale
namespace ZEllSheaf

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [IsNoetherian X]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

/-- The product of the underlying systems of two ℓ-adic sheaves satisfies the
ℓ-adic system laws. -/
instance instIsZEllSheafSystemProd (F G : ZEllSheaf X ℓ) :
    IsZEllSheafSystem X ℓ (F.system ⨯ G.system) := sorry

/-- The binary product of `ℤ_[ℓ]`-sheaves, computed stagewise on inverse systems. -/
def prod (F G : ZEllSheaf X ℓ) : ZEllSheaf X ℓ :=
  ofSystem (F.system ⨯ G.system)
    (instIsZEllSheafSystemProd F G).isKilled (instIsZEllSheafSystemProd F G).step_comp_nsmul
    (instIsZEllSheafSystemProd F G).isAdic (instIsZEllSheafSystemProd F G).isConstructible

/-- The underlying system of a binary product is the product of systems. -/
theorem prod_spec (F G : ZEllSheaf X ℓ) :
    (prod F G).system = (F.system ⨯ G.system) := sorry

/-- First projection of a binary product of `ℤ_[ℓ]`-sheaves. -/
def prodFst (F G : ZEllSheaf X ℓ) : Hom (prod F G) F :=
  homMk Limits.prod.fst

/-- Second projection of a binary product of `ℤ_[ℓ]`-sheaves. -/
def prodSnd (F G : ZEllSheaf X ℓ) : Hom (prod F G) G :=
  homMk Limits.prod.snd

/-- The binary fan of projections out of `prod F G`. -/
def prodFan (F G : ZEllSheaf X ℓ) : BinaryFan F G :=
  BinaryFan.mk (prodFst F G) (prodSnd F G)

/-- The pairing of two morphisms into a binary product of `ℤ_[ℓ]`-sheaves. -/
def prodLift {F G T : ZEllSheaf X ℓ} (f : Hom T F) (g : Hom T G) : Hom T (prod F G) :=
  homMk (Limits.prod.lift (hom f) (hom g))

/-- The pairing induced by a binary fan factors its two legs through the product fan. -/
theorem prodFan_fac (F G : ZEllSheaf X ℓ) (s : BinaryFan F G)
    (j : Discrete WalkingPair) :
    prodLift (BinaryFan.fst s) (BinaryFan.snd s) ≫ (prodFan F G).π.app j =
      s.π.app j := sorry

/-- A morphism factoring the legs of a binary fan through the product fan equals
the canonical pairing. -/
theorem prodFan_uniq (F G : ZEllSheaf X ℓ) (s : BinaryFan F G)
    (m : s.pt ⟶ (prodFan F G).pt)
    (h : ∀ j : Discrete WalkingPair, m ≫ (prodFan F G).π.app j = s.π.app j) :
    m = prodLift (BinaryFan.fst s) (BinaryFan.snd s) := sorry

/-- The named product fan is a limit cone. -/
def isLimit_prodFan (F G : ZEllSheaf X ℓ) :
    IsLimit (prodFan F G) where
  lift s := prodLift (BinaryFan.fst s) (BinaryFan.snd s)
  fac := prodFan_fac F G
  uniq := prodFan_uniq F G

/-- The zero inverse system satisfies the ℓ-adic system laws. -/
instance instIsZEllSheafSystemZero :
    IsZEllSheafSystem X ℓ
      (0 : SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) := sorry

/-- The zero `ℤ_[ℓ]`-sheaf, whose underlying inverse system is the zero system. -/
def zero : ZEllSheaf X ℓ :=
  ofSystem (0 : SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (instIsZEllSheafSystemZero (X := X) (ℓ := ℓ)).isKilled
    (instIsZEllSheafSystemZero (X := X) (ℓ := ℓ)).step_comp_nsmul
    (instIsZEllSheafSystemZero (X := X) (ℓ := ℓ)).isAdic
    (instIsZEllSheafSystemZero (X := X) (ℓ := ℓ)).isConstructible

/-- The underlying system of the zero sheaf is the zero inverse system. -/
theorem zero_system :
    (zero : ZEllSheaf X ℓ).system =
      (0 : SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) := sorry

/-- The zero `ℤ_[ℓ]`-sheaf is terminal. -/
def isTerminal_zero : IsTerminal (zero : ZEllSheaf X ℓ) :=
  IsTerminal.ofUniqueHom (fun F ↦ (0 : F ⟶ zero)) (fun _ _ ↦ sorry)

/-- Binary products of `ℤ_[ℓ]`-sheaves exist, with vertex `prod F G`. -/
instance instHasLimit_pair (F G : ZEllSheaf X ℓ) : HasLimit (pair F G) :=
  HasLimit.mk { cone := prodFan F G, isLimit := isLimit_prodFan F G }

/-- The category of `ℤ_[ℓ]`-sheaves has binary products. -/
instance instHasBinaryProducts : HasBinaryProducts (ZEllSheaf X ℓ) :=
  hasBinaryProducts_of_hasLimit_pair (ZEllSheaf X ℓ)

/-- The category of `ℤ_[ℓ]`-sheaves has a terminal object. -/
instance instHasTerminal : HasTerminal (ZEllSheaf X ℓ) :=
  IsTerminal.hasTerminal isTerminal_zero

/-- The category of `ℤ_[ℓ]`-sheaves has finite products. -/
instance instHasFiniteProducts : HasFiniteProducts (ZEllSheaf X ℓ) :=
  hasFiniteProducts_of_has_binary_and_terminal

/-- The inverse of the adic comparison of a `ℤ_[ℓ]`-sheaf at stage `n`. -/
def adicInv (K : ZEllSheaf X ℓ) (n : ℕ) :
    K.stage n ⟶ nsmulCokernel (K.stage (n + 1)) (ℓ ^ (n + 1)) :=
  @inv _ _ _ _ (K.adicCokernel n) (K.isAdic n)

/-- Multiplication by `b` vanishes after reduction from `Y / (b * m)` to `Y / b`. -/
theorem doubleNsmulCokernelCompare_comp_eq_zero
    (Y : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (m b : ℕ) :
    (b • 𝟙 (nsmulCokernel Y (b * m))) ≫ nsmulCokernelReduce Y m b = 0 := sorry

/-- The comparison `(Y / (b * m)) / b ⟶ Y / b` induced by nsmul reduction. -/
def doubleNsmulCokernelCompare
    (Y : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (m b : ℕ) :
    nsmulCokernel (nsmulCokernel Y (b * m)) b ⟶ nsmulCokernel Y b :=
  cokernel.desc (b • 𝟙 (nsmulCokernel Y (b * m))) (nsmulCokernelReduce Y m b)
    (doubleNsmulCokernelCompare_comp_eq_zero Y m b)

/-- Inverse of the `ℓ^{n+1}`-reduced successor map of a `ℤ_[ℓ]`-sheaf, from adicity. -/
def laterModNsmulStepInv (K : ZEllSheaf X ℓ) (n k : ℕ) :
    nsmulCokernel (K.stage (n + k)) (ℓ ^ (n + 1)) ⟶
      nsmulCokernel (K.stage (n + k + 1)) (ℓ ^ (n + 1)) :=
  let p := ℓ ^ (n + 1)
  let e : ℓ ^ (n + k + 1) = p * ℓ ^ k :=
    (congrArg (fun t ↦ ℓ ^ t) (Nat.succ_add n k).symm).trans (Nat.pow_add ℓ (n + 1) k)
  nsmulCokernelMap p (adicInv K (n + k)) ≫
    eqToHom (congrArg (fun Z ↦ nsmulCokernel Z p)
      (congrArg (nsmulCokernel (K.stage (n + k + 1))) e)) ≫
    doubleNsmulCokernelCompare (K.stage (n + k + 1)) (ℓ ^ k) p

/-- The cone maps from stage `n` to later `ℓ^{n+1}`-reductions of the same sheaf. -/
def toAddModNsmul (K : ZEllSheaf X ℓ) (n : ℕ) :
    ∀ k : ℕ, K.stage n ⟶ nsmulCokernel (K.stage (n + k)) (ℓ ^ (n + 1))
  | 0 => cokernel.π ((ℓ ^ (n + 1)) • 𝟙 (K.stage n))
  | k + 1 => toAddModNsmul K n k ≫ laterModNsmulStepInv K n k

/-- Component of the cone from stage `n` to the `ℓ^{n+1}`-reduced inverse system. -/
def ownModNsmulConeApp (K : ZEllSheaf X ℓ) (n m : ℕ) :
    K.stage n ⟶ nsmulCokernel (K.stage m) (ℓ ^ (n + 1)) :=
  if h : m ≤ n then
    K.transitionMap h ≫ cokernel.π ((ℓ ^ (n + 1)) • 𝟙 (K.stage m))
  else
    toAddModNsmul K n (m - n) ≫
      nsmulCokernelMap (ℓ ^ (n + 1))
        (eqToHom (congrArg K.stage (Nat.add_sub_of_le (Nat.not_le.mp h).le)))

/-- Factorization of a morphism killing `α` through the naive kernel system. -/
def toNaiveKerSystem {F G K : ZEllSheaf X ℓ} (α : Hom F G) (β : Hom K F)
    (h : β ≫ α = 0) :
    K.system ⟶ naiveKerSystem α :=
  kernel.lift (hom α) (hom β) (by
    exact congrArg (fun φ : Hom K G ↦ hom φ) h)

/-- Naive-kernel factorizations of maps from `ℤ_[ℓ]`-sheaves land in stable images. -/
theorem toNaiveKerSystem_app_comp_eq_zero {F G K : ZEllSheaf X ℓ}
    (α : Hom F G) (β : Hom K F) (h : β ≫ α = 0) (n : ℕ) :
    (toNaiveKerSystem α β h).app (op n) ≫ stableImageToCokernelProduct α n = 0 := sorry

/-- Stagewise factorization through the stable-image kernel of a morphism. -/
def toStableImageStage {F G K : ZEllSheaf X ℓ} (α : Hom F G) (β : Hom K F)
    (h : β ≫ α = 0) (n : ℕ) :
    K.stage n ⟶ stableImageStage α n :=
  kernel.lift (stableImageToCokernelProduct α n) ((toNaiveKerSystem α β h).app (op n))
    (toNaiveKerSystem_app_comp_eq_zero α β h n)

/-- Stage-`n` component of the universal map into `ker α`. -/
def kerLift_app {F G K : ZEllSheaf X ℓ} (α : Hom F G) (β : Hom K F)
    (h : β ≫ α = 0) (n : ℕ) :
    K.stage n ⟶ (ker α).stage n :=
  limit.lift ((stableImageSystem α).modNsmulSystem ℓ n)
    { pt := K.stage n
      π :=
        { app := fun m ↦
            ownModNsmulConeApp K n m.unop ≫
              nsmulCokernelMap (ℓ ^ (n + 1)) (toStableImageStage α β h m.unop)
          naturality := fun _ _ _ ↦ sorry } }

/-- Kernel lifts are natural with respect to successor transitions. -/
theorem kerLift_naturality {F G K : ZEllSheaf X ℓ} (α : Hom F G) (β : Hom K F)
    (h : β ≫ α = 0) (n : ℕ) :
    K.system.map (homOfLE (n.le_add_right 1)).op ≫ kerLift_app α β h n =
      kerLift_app α β h (n + 1) ≫ (ker α).system.map (homOfLE (n.le_add_right 1)).op :=
  sorry

/-- The universal morphism `K ⟶ ker α` induced by a morphism `K ⟶ F` killing `α`. -/
def kerLift {F G K : ZEllSheaf X ℓ} (α : Hom F G) (β : Hom K F) (h : β ≫ α = 0) :
    Hom K (ker α) :=
  homMk (NatTrans.ofOpSequence (kerLift_app α β h) (kerLift_naturality α β h))

/-- The kernel lift composes with the kernel inclusion to the original map. -/
theorem kerLift_comp_kerι {F G K : ZEllSheaf X ℓ} (α : Hom F G) (β : Hom K F)
    (h : β ≫ α = 0) :
    kerLift α β h ≫ kerι α = β := sorry

/-- The universal morphism `coker α ⟶ T` induced by a morphism `G ⟶ T` killed by `α`. -/
def cokerDesc {F G T : ZEllSheaf X ℓ} (α : Hom F G) (β : Hom G T) (h : α ≫ β = 0) :
    Hom (coker α) T :=
  homMk (cokernel.desc (hom α) (hom β) (by
    exact congrArg (fun φ : Hom F T ↦ hom φ) h))

/-- The cokernel description composes with the cokernel projection to the original map. -/
theorem cokerDesc_condition {F G T : ZEllSheaf X ℓ} (α : Hom F G) (β : Hom G T)
    (h : α ≫ β = 0) :
    cokerπ α ≫ cokerDesc α β h = β := sorry

/-- The kernel fork of a morphism of `ℤ_[ℓ]`-sheaves, with vertex `ker α`. -/
def kerFork {F G : ZEllSheaf X ℓ} (α : F ⟶ G) : KernelFork α :=
  KernelFork.ofι (kerι α) (ker_condition α)

/-- The canonical kernel lift factors all legs of a kernel fork through the
stable-image kernel fork. -/
theorem kerFork_fac {F G : ZEllSheaf X ℓ} (α : F ⟶ G) (s : KernelFork α)
    (j : WalkingParallelPair) :
    kerLift α (Fork.ι s) (KernelFork.condition s) ≫ (kerFork α).π.app j =
      s.π.app j := sorry

/-- A morphism factoring all legs through the stable-image kernel fork equals
the canonical kernel lift. -/
theorem kerFork_uniq {F G : ZEllSheaf X ℓ} (α : F ⟶ G) (s : KernelFork α)
    (m : s.pt ⟶ (kerFork α).pt)
    (h : ∀ j : WalkingParallelPair, m ≫ (kerFork α).π.app j = s.π.app j) :
    m = kerLift α (Fork.ι s) (KernelFork.condition s) := sorry

/-- The named kernel fork is a limit cone. -/
def isLimit_kerFork {F G : ZEllSheaf X ℓ} (α : F ⟶ G) :
    IsLimit (kerFork α) where
  lift s := kerLift α (Fork.ι s) (KernelFork.condition s)
  fac := kerFork_fac α
  uniq := kerFork_uniq α

/-- The category of `ℤ_[ℓ]`-sheaves has kernels. -/
instance instHasKernels : HasKernels (ZEllSheaf X ℓ) where
  has_limit := fun α ↦ HasLimit.mk { cone := kerFork α, isLimit := isLimit_kerFork α }

/-- The cokernel cofork of a morphism of `ℤ_[ℓ]`-sheaves, with vertex `coker α`. -/
def cokerCofork {F G : ZEllSheaf X ℓ} (α : F ⟶ G) : CokernelCofork α :=
  CokernelCofork.ofπ (cokerπ α) (coker_condition α)

/-- The canonical cokernel descent factors all legs of the stagewise cokernel
cofork through any cokernel cofork. -/
theorem cokerCofork_fac {F G : ZEllSheaf X ℓ} (α : F ⟶ G) (s : CokernelCofork α)
    (j : WalkingParallelPair) :
    (cokerCofork α).ι.app j ≫ cokerDesc α (Cofork.π s) (CokernelCofork.condition s) =
      s.ι.app j := sorry

/-- A morphism factoring all legs of the stagewise cokernel cofork equals
the canonical cokernel descent. -/
theorem cokerCofork_uniq {F G : ZEllSheaf X ℓ} (α : F ⟶ G) (s : CokernelCofork α)
    (m : (cokerCofork α).pt ⟶ s.pt)
    (h : ∀ j : WalkingParallelPair, (cokerCofork α).ι.app j ≫ m = s.ι.app j) :
    m = cokerDesc α (Cofork.π s) (CokernelCofork.condition s) := sorry

/-- The named cokernel cofork is a colimit cocone. -/
def isColimit_cokerCofork {F G : ZEllSheaf X ℓ} (α : F ⟶ G) :
    IsColimit (cokerCofork α) where
  desc s := cokerDesc α (Cofork.π s) (CokernelCofork.condition s)
  fac := cokerCofork_fac α
  uniq := cokerCofork_uniq α

/-- The category of `ℤ_[ℓ]`-sheaves has cokernels. -/
instance instHasCokernels : HasCokernels (ZEllSheaf X ℓ) where
  has_colimit := fun α ↦
    HasColimit.mk { cocone := cokerCofork α, isColimit := isColimit_cokerCofork α }

end ZEllSheaf
end AlgebraicGeometry.Scheme.Etale
