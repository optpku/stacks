/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int

/-!
# Multiplicativity of the integer-indexed Berthelot-Ogus eta operator

The divided-differential model makes multiplicativity degree-independent.  An element of
`eta f (eta g K)` is sent to `eta (f * g) K` by forgetting the intermediate subtype, and the
inverse rebuilds the two divisibility witnesses.  The public owner is formulated on
`Int.Domain (f * g)`, so regularity proofs are carried by the bundled complex rather than exposed
as arguments of every map.
@stack 0F7U
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CochainComplex.BerthelotOgus.Int

variable {A : Type u} [CommRing A]

namespace Mul

/-- Termwise regularity for a product implies termwise regularity for its left factor. -/
theorem leftRegular (f g : A) (K : Domain (f * g)) :
    IsTermwiseTorsionFree f K.obj := by
  intro i
  exact (IsSMulRegular.mul_iff.mp (K.property i)).1

/-- Termwise regularity for a product implies termwise regularity for its right factor. -/
theorem rightRegular (f g : A) (K : Domain (f * g)) :
    IsTermwiseTorsionFree g K.obj := by
  intro i
  exact (IsSMulRegular.mul_iff.mp (K.property i)).2

/-- The eta complex for the right factor, with regularity obtained from the product domain. -/
@[stacks 0F7U "right-factor eta complex"]
def rightEta (f g : A) (K : Domain (f * g)) : CochainComplex (ModuleCat.{v} A) ℤ :=
  eta g K.obj (rightRegular f g K)

/-- The right-factor eta complex remains termwise regular for the left factor. -/
theorem outerRegular (f g : A) (K : Domain (f * g)) :
    IsTermwiseTorsionFree f (rightEta f g K) := by
  intro i x y h
  apply Subtype.ext
  exact leftRegular f g K i (congrArg Subtype.val h)

/-- Applying eta first for `g` and then for `f` on the canonical product-regular domain. -/
@[stacks 0F7U "iterated integer-indexed eta complex"]
def iteratedEta (f g : A) (K : Domain (f * g)) : CochainComplex (ModuleCat.{v} A) ℤ :=
  eta f (rightEta f g K) (outerRegular f g K)

/-- Applying eta once for the product scalar on the canonical product-regular domain. -/
@[stacks 0F7U "product-scalar integer-indexed eta complex"]
def productEta (f g : A) (K : Domain (f * g)) : CochainComplex (ModuleCat.{v} A) ℤ :=
  eta (f * g) K.obj K.property

private theorem eta_d_smul_val (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (hK : IsTermwiseTorsionFree f K) (i : ℤ) (x : term f K i) :
    f • ((eta f K hK).d i (i + 1) x).1 = K.d i (i + 1) x.1 := by
  dsimp only [eta]
  rw [CochainComplex.of_d]
  change f • divideLinear f K i (hK.degree (i + 1)) x = K.d i (i + 1) x.1
  exact congrArg Subtype.val
    ((LinearEquiv.ofInjective (LinearMap.lsmul A (K.X (i + 1)) f)
      (hK.degree (i + 1))).apply_symm_apply (dToRange f K i x))

/-- Forgetting the intermediate right-factor subtype sends an iterated eta term into the eta term
for the product scalar. -/
theorem forward_mem (f g : A) (K : Domain (f * g)) (i : ℤ)
    (x : term f (rightEta f g K) i) : x.1.1 ∈ term (f * g) K.obj i := by
  obtain ⟨y, hy⟩ := (show ∃ y : term g K.obj (i + 1),
    f • y = (rightEta f g K).d i (i + 1) x.1 from x.property)
  have hy' : f • y.1 = ((rightEta f g K).d i (i + 1) x.1).1 :=
    congrArg Subtype.val hy
  change ∃ y : K.obj.X (i + 1), (f * g) • y = K.obj.d i (i + 1) x.1.1
  refine ⟨y.1, ?_⟩
  calc
    (f * g) • y.1 = g • (f • y.1) :=
      (mul_smul f g y.1).trans (smul_comm f g y.1)
    _ = g • ((rightEta f g K).d i (i + 1) x.1).1 :=
      congrArg (fun z : K.obj.X (i + 1) ↦ g • z) hy'
    _ = K.obj.d i (i + 1) x.1.1 :=
      eta_d_smul_val g K.obj (rightRegular f g K) i x.1

/-- The degreewise forward map from the iterated eta construction to eta for the product scalar. -/
@[stacks 0F7U "degreewise forward eta multiplicativity map"]
def forwardLinear (f g : A) (K : Domain (f * g)) (i : ℤ) :
    term f (rightEta f g K) i →ₗ[A] term (f * g) K.obj i :=
  ((term g K.obj i).subtype.comp (term f (rightEta f g K) i).subtype).codRestrict _
    (forward_mem f g K i)

/-- An eta term for `f * g` canonically determines an eta term for the right factor `g`. -/
theorem right_mem (f g : A) (K : Domain (f * g)) (i : ℤ)
    (x : term (f * g) K.obj i) : x.1 ∈ term g K.obj i := by
  obtain ⟨y, hy⟩ := (show ∃ y : K.obj.X (i + 1),
    (f * g) • y = K.obj.d i (i + 1) x.1 from x.property)
  change ∃ y : K.obj.X (i + 1), g • y = K.obj.d i (i + 1) x.1
  exact ⟨f • y, by simpa only [smul_smul, mul_comm g f] using hy⟩

/-- The degreewise map that regards an eta term for `f * g` as an eta term for `g`. -/
@[stacks 0F7U "right-factor map for eta multiplicativity"]
def rightLinear (f g : A) (K : Domain (f * g)) (i : ℤ) :
    term (f * g) K.obj i →ₗ[A] term g K.obj i :=
  (term (f * g) K.obj i).subtype.codRestrict _ (right_mem f g K i)

/-- Rebuilding the right-factor term from an `eta (f * g)` term also satisfies the outer
`eta f` divisibility condition. -/
theorem reverse_mem (f g : A) (K : Domain (f * g)) (i : ℤ)
    (x : term (f * g) K.obj i) :
    rightLinear f g K i x ∈ term f (rightEta f g K) i := by
  obtain ⟨y, hy⟩ := (show ∃ y : K.obj.X (i + 1),
    (f * g) • y = K.obj.d i (i + 1) x.1 from x.property)
  have hyzero : K.obj.d (i + 1) ((i + 1) + 1) y = 0 := by
    apply (K.property ((i + 1) + 1)).right_eq_zero_of_smul
    rw [← map_smul, hy]
    have h := congrArg (fun φ : K.obj.X i ⟶ K.obj.X ((i + 1) + 1) ↦ φ x.1)
      (K.obj.d_comp_d i (i + 1) ((i + 1) + 1))
    exact h
  have hymem : y ∈ term g K.obj (i + 1) := by
    change ∃ z : K.obj.X ((i + 1) + 1),
      g • z = K.obj.d (i + 1) ((i + 1) + 1) y
    exact ⟨0, by rw [hyzero, smul_zero]⟩
  change ∃ z : term g K.obj (i + 1),
    f • z = (rightEta f g K).d i (i + 1) (rightLinear f g K i x)
  refine ⟨⟨y, hymem⟩, ?_⟩
  apply Subtype.ext
  apply rightRegular f g K (i + 1)
  change g • (f • y) = g • ((rightEta f g K).d i (i + 1)
    (rightLinear f g K i x)).1
  calc
    g • (f • y) = K.obj.d i (i + 1) x.1 :=
      (smul_smul g f y).trans ((congrArg (fun a : A ↦ a • y)
        (mul_comm g f)).trans hy)
    _ = g • ((rightEta f g K).d i (i + 1) (rightLinear f g K i x)).1 :=
      (eta_d_smul_val g K.obj (rightRegular f g K) i (rightLinear f g K i x)).symm

/-- The degreewise inverse map from eta for the product scalar to the iterated eta construction. -/
@[stacks 0F7U "degreewise inverse eta multiplicativity map"]
def reverseLinear (f g : A) (K : Domain (f * g)) (i : ℤ) :
    term (f * g) K.obj i →ₗ[A] term f (rightEta f g K) i :=
  (rightLinear f g K i).codRestrict _ (reverse_mem f g K i)

/-- The bundled degreewise forward map for multiplicativity of integer-indexed eta. -/
@[stacks 0F7U "bundled degreewise forward eta map"]
def forwardHom (f g : A) (K : Domain (f * g)) (i : ℤ) :
    (iteratedEta f g K).X i ⟶ (productEta f g K).X i :=
  ModuleCat.ofHom (forwardLinear f g K i)

/-- The bundled degreewise inverse map for multiplicativity of integer-indexed eta. -/
@[stacks 0F7U "bundled degreewise inverse eta map"]
def reverseHom (f g : A) (K : Domain (f * g)) (i : ℤ) :
    (productEta f g K).X i ⟶ (iteratedEta f g K).X i :=
  ModuleCat.ofHom (reverseLinear f g K i)

/-- The degreewise forward maps commute with the divided differentials. -/
theorem forward_comm (f g : A) (K : Domain (f * g)) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    forwardHom f g K i ≫ (productEta f g K).d i j =
      (iteratedEta f g K).d i j ≫ forwardHom f g K j := by
  change i + 1 = j at hij
  subst j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply K.property (i + 1)
  have hf := congrArg Subtype.val
    (eta_d_smul_val f (rightEta f g K) (outerRegular f g K) i x)
  calc
    (f * g) • ((productEta f g K).d i (i + 1) (forwardHom f g K i x)).1 =
        K.obj.d i (i + 1) x.1.1 :=
      eta_d_smul_val (f * g) K.obj K.property i (forwardLinear f g K i x)
    _ = g • ((rightEta f g K).d i (i + 1) x.1).1 :=
      (eta_d_smul_val g K.obj (rightRegular f g K) i x.1).symm
    _ = g • (f • ((iteratedEta f g K).d i (i + 1) x).1.1) :=
      congrArg (fun y : K.obj.X (i + 1) ↦ g • y) hf.symm
    _ = (f * g) • ((iteratedEta f g K).d i (i + 1) x).1.1 := by
      rw [smul_smul, mul_comm g f]

/-- The degreewise inverse maps commute with the divided differentials. -/
theorem reverse_comm (f g : A) (K : Domain (f * g)) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    reverseHom f g K i ≫ (iteratedEta f g K).d i j =
      (productEta f g K).d i j ≫ reverseHom f g K j := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  have h := ConcreteCategory.congr_hom (forward_comm f g K i j hij)
    (reverseHom f g K i x)
  exact (congrArg Subtype.val h).symm

/-- The canonical comparison from iterated eta to eta for the product scalar. -/
@[stacks 0F7U "eta multiplicativity comparison"]
def comparison (f g : A) (K : Domain (f * g)) :
    iteratedEta f g K ⟶ productEta f g K where
  f i := forwardHom f g K i
  comm' i j hij := forward_comm f g K i j hij

/-- The explicit inverse comparison from eta for the product scalar to iterated eta. -/
@[stacks 0F7U "inverse eta multiplicativity comparison"]
def inverse (f g : A) (K : Domain (f * g)) :
    productEta f g K ⟶ iteratedEta f g K where
  f i := reverseHom f g K i
  comm' i j hij := reverse_comm f g K i j hij

/-- The multiplicativity comparison followed by its explicit inverse is the identity. -/
theorem comparison_inverse (f g : A) (K : Domain (f * g)) :
    comparison f g K ≫ inverse f g K = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- The explicit inverse followed by the multiplicativity comparison is the identity. -/
theorem inverse_comparison (f g : A) (K : Domain (f * g)) :
    inverse f g K ≫ comparison f g K = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- Applying the integer-indexed eta operator successively for `g` and `f` is canonically
isomorphic to applying it once for `f * g`.  The sole regularity input is carried by the bundled
object `K : Domain (f * g)`, and both directions are explicit subtype maps. -/
@[stacks 0F7U "multiplicativity of the integer-indexed Berthelot-Ogus eta operator"]
def iso (f g : A) (K : Domain (f * g)) : iteratedEta f g K ≅ productEta f g K where
  hom := comparison f g K
  inv := inverse f g K
  hom_inv_id := comparison_inverse f g K
  inv_hom_id := inverse_comparison f g K

/-- Unbundled access to the integer-indexed eta multiplicativity isomorphism. -/
@[stacks 0F7U "eta multiplicativity from an explicit regularity proof"]
def isoOfRegular (f g : A) (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (hK : IsTermwiseTorsionFree (f * g) K) :
    iteratedEta f g (⟨K, hK⟩ : Domain (f * g)) ≅
      productEta f g (⟨K, hK⟩ : Domain (f * g)) :=
  iso f g ⟨K, hK⟩

end Mul

end CochainComplex.BerthelotOgus.Int
