module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.EqToHom
public import stacks_project.Chap64.Lemma_64_18_3_Category
public import stacks_project.Chap64.Lemma_64_18_3_Kernel

/-!
# Abelian instance for ℤ_[ℓ]-sheaves

Finite products and zero objects of `ℤ_[ℓ]`-sheaves are computed stagewise on the
underlying inverse systems. Kernels and cokernels are the named `ker`/`coker`
constructions, and the coimage-image comparison is an isomorphism.
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

/-- The binary product of `ℤ_[ℓ]`-sheaves, computed stagewise on inverse systems. -/
def prod (F G : ZEllSheaf X ℓ) : ZEllSheaf X ℓ where
  system := F.system ⨯ G.system
  isKilled := sorry
  step_comp_nsmul := sorry
  isAdic := sorry
  isConstructible := sorry

/-- The underlying system of a binary product is the product of systems. -/
theorem prod_spec (F G : ZEllSheaf X ℓ) :
    (prod F G).system = (F.system ⨯ G.system) := sorry

/-- First projection of a binary product of `ℤ_[ℓ]`-sheaves. -/
def prodFst (F G : ZEllSheaf X ℓ) : Hom (prod F G) F :=
  Limits.prod.fst

/-- Second projection of a binary product of `ℤ_[ℓ]`-sheaves. -/
def prodSnd (F G : ZEllSheaf X ℓ) : Hom (prod F G) G :=
  Limits.prod.snd

/-- The binary fan of projections out of `prod F G`. -/
def prodFan (F G : ZEllSheaf X ℓ) : BinaryFan F G :=
  BinaryFan.mk (prodFst F G) (prodSnd F G)

/-- The pairing of two morphisms into a binary product of `ℤ_[ℓ]`-sheaves. -/
def prodLift {F G T : ZEllSheaf X ℓ} (f : Hom T F) (g : Hom T G) : Hom T (prod F G) :=
  Limits.prod.lift (f : T.system ⟶ F.system) (g : T.system ⟶ G.system)

/-- The named product fan is a limit cone. -/
def isLimit_prodFan (F G : ZEllSheaf X ℓ) :
    IsLimit (prodFan F G) where
  lift s := prodLift (BinaryFan.fst s) (BinaryFan.snd s)
  fac := sorry
  uniq := sorry

/-- The zero `ℤ_[ℓ]`-sheaf, whose underlying inverse system is the zero system. -/
def zero : ZEllSheaf X ℓ where
  system := (0 : SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
  isKilled := sorry
  step_comp_nsmul := sorry
  isAdic := sorry
  isConstructible := sorry

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
  kernel.lift (α : F.system ⟶ G.system) (β : K.system ⟶ F.system) h

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
  NatTrans.ofOpSequence (kerLift_app α β h) (kerLift_naturality α β h)

/-- The kernel lift composes with the kernel inclusion to the original map. -/
theorem kerLift_comp_kerι {F G K : ZEllSheaf X ℓ} (α : Hom F G) (β : Hom K F)
    (h : β ≫ α = 0) :
    kerLift α β h ≫ kerι α = β := sorry

/-- The universal morphism `coker α ⟶ T` induced by a morphism `G ⟶ T` killed by `α`. -/
def cokerDesc {F G T : ZEllSheaf X ℓ} (α : Hom F G) (β : Hom G T) (h : α ≫ β = 0) :
    Hom (coker α) T :=
  cokernel.desc (α : F.system ⟶ G.system) (β : G.system ⟶ T.system) h

/-- The cokernel description composes with the cokernel projection to the original map. -/
theorem cokerDesc_condition {F G T : ZEllSheaf X ℓ} (α : Hom F G) (β : Hom G T)
    (h : α ≫ β = 0) :
    cokerπ α ≫ cokerDesc α β h = β := sorry

/-- The kernel fork of a morphism of `ℤ_[ℓ]`-sheaves, with vertex `ker α`. -/
def kerFork {F G : ZEllSheaf X ℓ} (α : F ⟶ G) : KernelFork α :=
  KernelFork.ofι (kerι α) (ker_condition α)

/-- The named kernel fork is a limit cone. -/
def isLimit_kerFork {F G : ZEllSheaf X ℓ} (α : F ⟶ G) :
    IsLimit (kerFork α) where
  lift s := kerLift α (Fork.ι s) (KernelFork.condition s)
  fac := sorry
  uniq := sorry

/-- The category of `ℤ_[ℓ]`-sheaves has kernels. -/
instance instHasKernels : HasKernels (ZEllSheaf X ℓ) where
  has_limit := fun α ↦ HasLimit.mk { cone := kerFork α, isLimit := isLimit_kerFork α }

/-- The cokernel cofork of a morphism of `ℤ_[ℓ]`-sheaves, with vertex `coker α`. -/
def cokerCofork {F G : ZEllSheaf X ℓ} (α : F ⟶ G) : CokernelCofork α :=
  CokernelCofork.ofπ (cokerπ α) (coker_condition α)

/-- The named cokernel cofork is a colimit cocone. -/
def isColimit_cokerCofork {F G : ZEllSheaf X ℓ} (α : F ⟶ G) :
    IsColimit (cokerCofork α) where
  desc s := cokerDesc α (Cofork.π s) (CokernelCofork.condition s)
  fac := sorry
  uniq := sorry

/-- The category of `ℤ_[ℓ]`-sheaves has cokernels. -/
instance instHasCokernels : HasCokernels (ZEllSheaf X ℓ) where
  has_colimit := fun α ↦
    HasColimit.mk { cocone := cokerCofork α, isColimit := isColimit_cokerCofork α }

/-- The abelian coimage-image comparison of a morphism of `ℤ_[ℓ]`-sheaves is an
isomorphism. -/
instance instIsIso_coimageImageComparison {F G : ZEllSheaf X ℓ} (α : F ⟶ G) :
    IsIso (Abelian.coimageImageComparison α) := sorry

/-- The category of `ℤ_[ℓ]`-sheaves on a Noetherian scheme is abelian. -/
instance instAbelian : Abelian (ZEllSheaf X ℓ) :=
  Abelian.ofCoimageImageComparisonIsIso


end ZEllSheaf
end AlgebraicGeometry.Scheme.Etale
