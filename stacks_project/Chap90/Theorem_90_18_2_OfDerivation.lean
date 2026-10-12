/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.RingTheory.Derivation.Basic
public import stacks_project.Chap90.Definition_90_10_1_DualNumber
public import stacks_project.Chap90.Example_90_11_10_TangentSpace
public import stacks_project.Chap90.Lemma_90_26_2_LinearMap

/-!
# Canonical map from derivations to a functor tangent space

A `Λ`-derivation `D : Derivation Λ k k` determines the morphism
`derivationToDualNumber D : residue Λ k ⟶ dualNumber Λ k` given by
`a ↦ inl a + inr (D a)`. For a predeformation functor `F`, the canonical map
`γ : Derivation Λ k k → tangentSpace F` is `F.map (derivationToDualNumber D)`
applied to the unique residue value.
-/

@[expose] public section

noncomputable section

open CategoryTheory ArtinianLocalAlgCat TrivSqZeroExt

universe u v

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

end ArtinianLocalAlgCat

namespace CategoryTheory.Functor.IsPredeformationFunctor

/-- The unique residue-field value of a predeformation functor. -/
def residuePoint (F : ArtinianLocalAlgCat Λ k ⥤ Type v) [IsPredeformationFunctor F] :
    F.obj (residue Λ k) :=
  (Classical.choice unique_residue).default

/-- Any residue-field value of a predeformation functor equals `residuePoint F`. -/
theorem residuePoint_eq (F : ArtinianLocalAlgCat Λ k ⥤ Type v) [IsPredeformationFunctor F]
    (x : F.obj (residue Λ k)) : x = residuePoint F := sorry

/-- The canonical map `γ : Derivation Λ k k → tangentSpace F` sending `D` to the
pushforward of the unique residue value along `derivationToDualNumber D`. -/
def ofDerivation (F : ArtinianLocalAlgCat Λ k ⥤ Type v) [IsPredeformationFunctor F] :
    Derivation Λ k k → tangentSpace F :=
  fun D ↦ F.map (derivationToDualNumber D) (residuePoint F)

/-- `ofDerivation F D` is the pushforward of any residue-field value along
`derivationToDualNumber D`. -/
theorem ofDerivation_apply (F : ArtinianLocalAlgCat Λ k ⥤ Type v)
    [IsPredeformationFunctor F] (x0 : F.obj (residue Λ k)) (D : Derivation Λ k k) :
    ofDerivation F D = F.map (derivationToDualNumber D) x0 := sorry

/-- The map `γ` as a bundled `k`-linear map, when `F` satisfies Schlessinger's (H2). -/
def ofDerivationLinear (F : ArtinianLocalAlgCat Λ k ⥤ Type v)
    [IsPredeformationFunctor F] [HasSchlessingerH2 F] :
    Derivation Λ k k →ₗ[k] tangentSpace F where
  toFun := ofDerivation F
  map_add' := sorry
  map_smul' := sorry

/-- The underlying function of `ofDerivationLinear` is `ofDerivation`. -/
theorem ofDerivationLinear_apply (F : ArtinianLocalAlgCat Λ k ⥤ Type v)
    [IsPredeformationFunctor F] [HasSchlessingerH2 F] (D : Derivation Λ k k) :
    ofDerivationLinear F D = ofDerivation F D := sorry

end CategoryTheory.Functor.IsPredeformationFunctor

end
