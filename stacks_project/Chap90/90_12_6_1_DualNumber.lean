module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.Derivation.Basic
public import stacks_project.Chap90.Definition_90_6_2_Predeformation
public import stacks_project.Chap90.Definition_90_12_1_DualNumber

/-!
# Dual-number morphisms associated to derivations

A `Λ`-derivation `D : Derivation Λ k k` determines the morphism `f_D : k ⟶ k[ε]` of `C_Λ`
given by `a ↦ inl a + inr (D a)`, and conversely. This identifies
`Mor_{C_Λ}(k, k[ε])` with `Der_Λ(k, k)`.
-/

@[expose] public section

open CategoryTheory TrivSqZeroExt

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

/-- The morphism `f_D : residue Λ k ⟶ dualNumber Λ k` of `C_Λ` associated to a derivation
`D : Derivation Λ k k`, given on underlying algebras by `a ↦ inl a + inr (D a)`. -/
def derivationToDualNumber (D : Derivation Λ k k) : residue Λ k ⟶ dualNumber Λ k where
  hom :=
    { toFun := fun a ↦ inl a + inr (D a)
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry
      commutes' := sorry }
  isLocalHom := sorry
  residue_compat := sorry

/-- `derivationToDualNumber D` evaluates to the dual number with scalar `a` and infinitesimal
`D a`. -/
theorem derivationToDualNumber_apply (D : Derivation Λ k k) (a : k) :
    (derivationToDualNumber D).hom a = inl a + inr (D a) := sorry

/-- The `Λ`-derivation associated to a morphism `f : residue Λ k ⟶ dualNumber Λ k`, given by
the infinitesimal coefficient `a ↦ snd (f.hom a)`. -/
def derivationOfHom (f : residue Λ k ⟶ dualNumber Λ k) : Derivation Λ k k where
  toFun := fun a ↦ snd (f.hom a)
  map_add' := sorry
  map_smul' := sorry
  map_one_eq_zero' := sorry
  leibniz' := sorry

/-- `derivationOfHom f` extracts the infinitesimal coefficient of `f.hom`. -/
theorem derivationOfHom_apply (f : residue Λ k ⟶ dualNumber Λ k) (a : k) :
    derivationOfHom f a = snd (f.hom a) := sorry

/-- Morphisms `residue Λ k ⟶ dualNumber Λ k` in `C_Λ` are identified with derivations
`Derivation Λ k k`. -/
def derivationHomEquiv (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] : Derivation Λ k k ≃ (residue Λ k ⟶ dualNumber Λ k) where
  toFun := derivationToDualNumber
  invFun := derivationOfHom
  left_inv := sorry
  right_inv := sorry

/-- `derivationHomEquiv` sends a derivation to the associated dual-number morphism. -/
theorem derivationHomEquiv_apply (D : Derivation Λ k k) :
    derivationHomEquiv Λ k D = derivationToDualNumber D := sorry

/-- The inverse of `derivationHomEquiv` recovers the derivation of a dual-number morphism. -/
theorem derivationHomEquiv_symm_apply (f : residue Λ k ⟶ dualNumber Λ k) :
    (derivationHomEquiv Λ k).symm f = derivationOfHom f := sorry

end ArtinianLocalAlgCat
