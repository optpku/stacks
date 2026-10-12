/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta

/-!
# Multiplicativity of the Berthelot-Ogus eta operator

This file records the composition law for the eta operator on nonnegative cochain complexes.  The
statement is made at the `ℕ`-indexed owner, where powers in degree `n` are literally `f ^ n`.
@stack 0F7U
-/

@[expose] public section

open CategoryTheory
open scoped BerthelotOgus

universe u v

namespace CochainComplex.BerthelotOgus.Nat

variable {A : Type u} [CommRing A]

namespace Mul

/-- Forgetting the intermediate `η[g]` subtype sends an iterated eta term into the eta term for
`f * g`. -/
theorem forward_mem (f g : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    (x : term f (η[g] K) n) :
    x.1.1 ∈ term (f * g) K n := sorry

/-- The degreewise forward map from the iterated eta construction to the eta construction for the
product scalar. -/
def forwardLinear (f g : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    term f (η[g] K) n →ₗ[A] term (f * g) K n :=
  ((term g K n).subtype.comp (term f (η[g] K) n).subtype).codRestrict _
    (forward_mem f g K n)

/-- An element of the eta term for `f * g` lies in the eta term for the right factor `g`. -/
theorem right_mem (f g : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    (x : term (f * g) K n) : x.1 ∈ term g K n := sorry

/-- The degreewise map that regards an eta term for `f * g` as an eta term for `g`. -/
def rightLinear (f g : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    term (f * g) K n →ₗ[A] term g K n :=
  (term (f * g) K n).subtype.codRestrict _ (right_mem f g K n)

/-- Under termwise `(f * g)`-torsion-freeness, the right-factor term obtained from an
`η[f * g]` term lies in the outer `η[f]` term. -/
theorem reverse_mem (f g : A) (K : CochainComplex (ModuleCat.{v} A) ℕ)
    (hK : IsTermwiseTorsionFree (f * g) K) (n : ℕ) (x : term (f * g) K n) :
    rightLinear f g K n x ∈ term f (η[g] K) n := sorry

/-- The degreewise inverse map from the eta construction for `f * g` to the iterated eta
construction.  Its underlying element is unchanged. -/
def reverseLinear (f g : A) (K : CochainComplex (ModuleCat.{v} A) ℕ)
    (hK : IsTermwiseTorsionFree (f * g) K) (n : ℕ) :
    term (f * g) K n →ₗ[A] term f (η[g] K) n :=
  (rightLinear f g K n).codRestrict _ (reverse_mem f g K hK n)

/-- The bundled degreewise forward map for multiplicativity of eta. -/
def forwardHom (f g : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    (η[f] (η[g] K)).X n ⟶ (η[f * g] K).X n :=
  ModuleCat.ofHom (forwardLinear f g K n)

/-- The bundled degreewise inverse map for multiplicativity of eta. -/
def reverseHom (f g : A) (K : CochainComplex (ModuleCat.{v} A) ℕ)
    (hK : IsTermwiseTorsionFree (f * g) K) (n : ℕ) :
    (η[f * g] K).X n ⟶ (η[f] (η[g] K)).X n :=
  ModuleCat.ofHom (reverseLinear f g K hK n)

/-- The degreewise forward maps commute with the eta differentials. -/
theorem forward_comm (f g : A) (K : CochainComplex (ModuleCat.{v} A) ℕ)
    (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j) :
    forwardHom f g K i ≫ (η[f * g] K).d i j =
      (η[f] (η[g] K)).d i j ≫ forwardHom f g K j := sorry

/-- The degreewise inverse maps commute with the eta differentials. -/
theorem reverse_comm (f g : A) (K : CochainComplex (ModuleCat.{v} A) ℕ)
    (hK : IsTermwiseTorsionFree (f * g) K)
    (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j) :
    reverseHom f g K hK i ≫ (η[f] (η[g] K)).d i j =
      (η[f * g] K).d i j ≫ reverseHom f g K hK j := sorry

/-- The canonical comparison from the iterated eta construction to the eta construction for the
product scalar. -/
def comparison (f g : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) :
    η[f] (η[g] K) ⟶ η[f * g] K where
  f n := forwardHom f g K n
  comm' i j hij := forward_comm f g K i j hij

/-- The explicit inverse comparison from the eta construction for the product scalar to the
iterated eta construction. -/
def inverse (f g : A) (K : CochainComplex (ModuleCat.{v} A) ℕ)
    (hK : IsTermwiseTorsionFree (f * g) K) :
    η[f * g] K ⟶ η[f] (η[g] K) where
  f n := reverseHom f g K hK n
  comm' i j hij := reverse_comm f g K hK i j hij

/-- The multiplicativity comparison followed by its explicit inverse is the identity. -/
theorem comparison_inverse (f g : A) (K : CochainComplex (ModuleCat.{v} A) ℕ)
    (hK : IsTermwiseTorsionFree (f * g) K) :
    comparison f g K ≫ inverse f g K hK = 𝟙 _ := sorry

/-- The explicit inverse followed by the multiplicativity comparison is the identity. -/
theorem inverse_comparison (f g : A) (K : CochainComplex (ModuleCat.{v} A) ℕ)
    (hK : IsTermwiseTorsionFree (f * g) K) :
    inverse f g K hK ≫ comparison f g K = 𝟙 _ := sorry

/-- Applying the eta operator successively for `g` and `f` is canonically isomorphic to applying
it once for `f * g`, provided multiplication by `f * g` is injective in every degree.  Both
directions are explicit subtype maps. -/
@[stacks 0F7U "multiplicativity of the Berthelot-Ogus eta operator"]
def iso (f g : A) (K : CochainComplex (ModuleCat.{v} A) ℕ)
    (hK : IsTermwiseTorsionFree (f * g) K) :
    η[f] (η[g] K) ≅ η[f * g] K where
  hom := comparison f g K
  inv := inverse f g K hK
  hom_inv_id := comparison_inverse f g K hK
  inv_hom_id := inverse_comparison f g K hK

end Mul

end CochainComplex.BerthelotOgus.Nat
