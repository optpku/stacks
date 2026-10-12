/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
    IsTermwiseTorsionFree f K.obj := sorry

/-- Termwise regularity for a product implies termwise regularity for its right factor. -/
theorem rightRegular (f g : A) (K : Domain (f * g)) :
    IsTermwiseTorsionFree g K.obj := sorry

/-- The eta complex for the right factor, with regularity obtained from the product domain. -/
@[stacks 0F7U "right-factor eta complex"]
def rightEta (f g : A) (K : Domain (f * g)) : CochainComplex (ModuleCat.{v} A) ℤ :=
  eta g K.obj (rightRegular f g K)

/-- The right-factor eta complex remains termwise regular for the left factor. -/
theorem outerRegular (f g : A) (K : Domain (f * g)) :
    IsTermwiseTorsionFree f (rightEta f g K) := sorry

/-- Applying eta first for `g` and then for `f` on the canonical product-regular domain. -/
@[stacks 0F7U "iterated integer-indexed eta complex"]
def iteratedEta (f g : A) (K : Domain (f * g)) : CochainComplex (ModuleCat.{v} A) ℤ :=
  eta f (rightEta f g K) (outerRegular f g K)

/-- Applying eta once for the product scalar on the canonical product-regular domain. -/
@[stacks 0F7U "product-scalar integer-indexed eta complex"]
def productEta (f g : A) (K : Domain (f * g)) : CochainComplex (ModuleCat.{v} A) ℤ :=
  eta (f * g) K.obj K.property

/-- Forgetting the intermediate right-factor subtype sends an iterated eta term into the eta term
for the product scalar. -/
theorem forward_mem (f g : A) (K : Domain (f * g)) (i : ℤ)
    (x : term f (rightEta f g K) i) : x.1.1 ∈ term (f * g) K.obj i := sorry

/-- The degreewise forward map from the iterated eta construction to eta for the product scalar. -/
@[stacks 0F7U "degreewise forward eta multiplicativity map"]
def forwardLinear (f g : A) (K : Domain (f * g)) (i : ℤ) :
    term f (rightEta f g K) i →ₗ[A] term (f * g) K.obj i :=
  ((term g K.obj i).subtype.comp (term f (rightEta f g K) i).subtype).codRestrict _
    (forward_mem f g K i)

/-- An eta term for `f * g` canonically determines an eta term for the right factor `g`. -/
theorem right_mem (f g : A) (K : Domain (f * g)) (i : ℤ)
    (x : term (f * g) K.obj i) : x.1 ∈ term g K.obj i := sorry

/-- The degreewise map that regards an eta term for `f * g` as an eta term for `g`. -/
@[stacks 0F7U "right-factor map for eta multiplicativity"]
def rightLinear (f g : A) (K : Domain (f * g)) (i : ℤ) :
    term (f * g) K.obj i →ₗ[A] term g K.obj i :=
  (term (f * g) K.obj i).subtype.codRestrict _ (right_mem f g K i)

/-- Rebuilding the right-factor term from an `eta (f * g)` term also satisfies the outer
`eta f` divisibility condition. -/
theorem reverse_mem (f g : A) (K : Domain (f * g)) (i : ℤ)
    (x : term (f * g) K.obj i) :
    rightLinear f g K i x ∈ term f (rightEta f g K) i := sorry

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
      (iteratedEta f g K).d i j ≫ forwardHom f g K j := sorry

/-- The degreewise inverse maps commute with the divided differentials. -/
theorem reverse_comm (f g : A) (K : Domain (f * g)) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    reverseHom f g K i ≫ (iteratedEta f g K).d i j =
      (productEta f g K).d i j ≫ reverseHom f g K j := sorry

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
    comparison f g K ≫ inverse f g K = 𝟙 _ := sorry

/-- The explicit inverse followed by the multiplicativity comparison is the identity. -/
theorem inverse_comparison (f g : A) (K : Domain (f * g)) :
    inverse f g K ≫ comparison f g K = 𝟙 _ := sorry

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
