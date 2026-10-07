module

public import Mathlib.RingTheory.Derivation.Basic
public import stacks_project.Chap90.Lemma_90_12_2_SquareZero

/-!
# Square-zero morphisms associated to derivations

A `Λ`-derivation `D : Derivation Λ k V` determines the automorphism `f_{1,D}` of
`k[V]` in `C_Λ` sending `a + v` to `a + (v + D a)`, and the morphism
`f_D : k ⟶ k[V]` obtained by composing with the canonical inclusion `k ⟶ k[V]`.
-/

@[expose] public section

open CategoryTheory TrivSqZeroExt

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

noncomputable section

namespace ArtinianLocalAlgCat

variable {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
  [Module Λ V] [IsScalarTower Λ k V]

/-- The morphism `f_{1,D} : k[V] ⟶ k[V]` of `C_Λ` associated to a derivation
`D : Derivation Λ k V`, given on underlying algebras by `a + v ↦ a + (v + D a)`. -/
def squareZeroAut (D : Derivation Λ k V) : squareZero Λ k V ⟶ squareZero Λ k V where
  hom :=
    { toFun := fun x ↦ inl x.fst + inr (x.snd + D x.fst)
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry
      commutes' := sorry }
  isLocalHom := sorry
  residue_compat := sorry

/-- `squareZeroAut D` evaluates to `inl x.fst + inr (x.snd + D x.fst)`. -/
theorem squareZeroAut_apply (D : Derivation Λ k V) (x : (squareZero Λ k V).carrier) :
    (squareZeroAut D).hom x = inl x.fst + inr (x.snd + D x.fst) := sorry

/-- The morphism `f_D : k ⟶ k[V]` of `C_Λ` associated to a derivation
`D : Derivation Λ k V`, obtained as `f_{1,D} ∘ f_0`. -/
def derivationToSquareZero (D : Derivation Λ k V) : residue Λ k ⟶ squareZero Λ k V :=
  residueToSquareZero V ≫ squareZeroAut D

/-- `derivationToSquareZero D` is the composite of `residueToSquareZero` with
`squareZeroAut D`. -/
theorem derivationToSquareZero_eq_comp (D : Derivation Λ k V) :
    derivationToSquareZero D = residueToSquareZero V ≫ squareZeroAut D := sorry

/-- `derivationToSquareZero D` evaluates to `inl a + inr (D a)`. -/
theorem derivationToSquareZero_apply (D : Derivation Λ k V) (a : k) :
    (derivationToSquareZero D).hom a = inl a + inr (D a) := sorry

/-- The square-zero automorphism associated to the zero derivation is the identity of
`k[V]`. -/
theorem squareZeroAut_zero :
    squareZeroAut (0 : Derivation Λ k V) = 𝟙 (squareZero Λ k V) := sorry

/-- Composition of square-zero automorphisms adds the corresponding derivations:
`f_{1,D} ∘ f_{1,D'} = f_{1, D + D'}`. -/
theorem squareZeroAut_add (D D' : Derivation Λ k V) :
    squareZeroAut D' ≫ squareZeroAut D = squareZeroAut (D + D') := sorry

/-- The automorphism `f_{1,D}` of `k[V]` in `C_Λ`, with inverse `f_{1,-D}`. -/
def squareZeroAutIso (D : Derivation Λ k V) : squareZero Λ k V ≅ squareZero Λ k V where
  hom := squareZeroAut D
  inv := squareZeroAut (-D)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The underlying morphism of `squareZeroAutIso D` is `squareZeroAut D`. -/
theorem squareZeroAutIso_hom (D : Derivation Λ k V) :
    (squareZeroAutIso D).hom = squareZeroAut D := sorry

/-- The inverse of `squareZeroAutIso D` is `squareZeroAut (-D)`. -/
theorem squareZeroAutIso_inv (D : Derivation Λ k V) :
    (squareZeroAutIso D).inv = squareZeroAut (-D) := sorry

end ArtinianLocalAlgCat

end
