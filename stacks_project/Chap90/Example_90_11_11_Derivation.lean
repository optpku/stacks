/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.RingTheory.Derivation.Basic
public import stacks_project.Chap90.«90_17_5_3_SquareZero»
public import stacks_project.Chap90.Definition_90_6_1_Prorepresentable
public import stacks_project.Chap90.Example_90_11_10_TangentSpace
public import stacks_project.Chap90.Example_90_16_10_ResidueHom
public import stacks_project.Chap90.Lemma_90_4_4_TensorCompletion
public import stacks_project.Chap90.Lemma_90_4_5_Residue

/-!
# Morphisms into square-zero extensions as derivations

A morphism `S ⟶ k[V]` in `CompleteLocalAlgCat Λ k` compatible with residue
augmentations corresponds to a `Λ`-derivation `S → V`, via
`D s = (f.hom s).snd` and `f s = inl (residueFieldHom S s) + inr (D s)`.
-/

@[expose] public section

open CategoryTheory TrivSqZeroExt

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

noncomputable section

namespace CompleteLocalAlgCat

/-- Restrict scalars from `k` to `S` along the residue identification, making a
`k`-module into an `S`-module. -/
instance (priority := 80) instModule_carrier_of_residue (S : CompleteLocalAlgCat Λ k)
    (V : Type u) [AddCommGroup V] [Module k V] : Module S.carrier V :=
  Module.compHom V (residueFieldHom S).toRingHom

/-- The tower `Λ → S → V` for the residue `S`-action `instModule_carrier_of_residue`,
assuming the `Λ`-action on `V` is restriction of scalars along `algebraMap Λ k`. -/
instance instIsScalarTower_carrier_residue_module (S : CompleteLocalAlgCat Λ k)
    (V : Type u) [AddCommGroup V] [Module k V] [Module Λ V] [IsScalarTower Λ k V] :
    IsScalarTower Λ S.carrier V := sorry

/-- The `k`-action commutes with the residue-induced `S`-action
`instModule_carrier_of_residue`. -/
instance instSMulCommClass_residue_module (S : CompleteLocalAlgCat Λ k)
    (V : Type u) [AddCommGroup V] [Module k V] :
    SMulCommClass k S.carrier V := sorry

/-- The derivation associated to a residue-compatible map `f : S ⟶ k[V]`, given by
`D s = (f.hom s).snd`. -/
def homToDerivation (S : CompleteLocalAlgCat Λ k) (V : Type u)
    [AddCommGroup V] [Module k V] [Module Λ V] [IsScalarTower Λ k V] [Module.Finite k V]
    (f : S ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.squareZero Λ k V)) :
    Derivation Λ S.carrier V where
  toFun s := (f.hom s).snd
  map_add' := sorry
  map_smul' := sorry
  map_one_eq_zero' := sorry
  leibniz' := sorry

/-- `homToDerivation f` evaluates as the infinitesimal component of `f`. -/
theorem homToDerivation_apply (S : CompleteLocalAlgCat Λ k) (V : Type u)
    [AddCommGroup V] [Module k V] [Module Λ V] [IsScalarTower Λ k V] [Module.Finite k V]
    (f : S ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.squareZero Λ k V))
    (s : S.carrier) :
    homToDerivation S V f s = (f.hom s).snd := sorry

/-- The `Ĉ_Λ`-morphism `S ⟶ k[V]` associated to a derivation `D`, given by
`f s = inl (residueFieldHom S s) + inr (D s)`. -/
def derivationToHom (S : CompleteLocalAlgCat Λ k) (V : Type u)
    [AddCommGroup V] [Module k V] [Module Λ V] [IsScalarTower Λ k V] [Module.Finite k V]
    (D : Derivation Λ S.carrier V) :
    S ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.squareZero Λ k V) where
  hom :=
    { toFun := fun s ↦ inl (residueFieldHom S s) + inr (D s)
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry
      commutes' := sorry }
  isLocalHom := sorry
  residue_compat := sorry

/-- `derivationToHom D` evaluates to the square-zero element with residue `q s` and
infinitesimal `D s`. -/
theorem derivationToHom_apply (S : CompleteLocalAlgCat Λ k) (V : Type u)
    [AddCommGroup V] [Module k V] [Module Λ V] [IsScalarTower Λ k V] [Module.Finite k V]
    (D : Derivation Λ S.carrier V) (s : S.carrier) :
    (derivationToHom S V D).hom s = inl (residueFieldHom S s) + inr (D s) := sorry

/-- The morphism associated to a derivation is compatible with the augmentations
`S ⟶ k` and `k[V] ⟶ k`. -/
theorem derivationToHom_comp_squareZeroToResidue (S : CompleteLocalAlgCat Λ k)
    (V : Type u) [AddCommGroup V] [Module k V] [Module Λ V] [IsScalarTower Λ k V] [Module.Finite k V]
    (D : Derivation Λ S.carrier V) :
    derivationToHom S V D ≫
        ArtinianLocalAlgCat.inclusion.map (ArtinianLocalAlgCat.squareZeroToResidue Λ k V) =
      residueHom S := sorry

/-- Morphisms `S ⟶ k[V]` in `Ĉ_Λ` are equivalent to `Λ`-derivations `S → V`. -/
def homEquivDerivation (S : CompleteLocalAlgCat Λ k) (V : Type u)
    [AddCommGroup V] [Module k V] [Module Λ V] [IsScalarTower Λ k V] [Module.Finite k V] :
    (S ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.squareZero Λ k V)) ≃
      Derivation Λ S.carrier V :=
  Equiv.mk (homToDerivation S V) (derivationToHom S V) sorry sorry

/-- `homEquivDerivation` sends a morphism to the associated derivation. -/
theorem homEquivDerivation_apply (S : CompleteLocalAlgCat Λ k) (V : Type u)
    [AddCommGroup V] [Module k V] [Module Λ V] [IsScalarTower Λ k V] [Module.Finite k V]
    (f : S ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.squareZero Λ k V)) :
    homEquivDerivation S V f = homToDerivation S V f := sorry

/-- The inverse of `homEquivDerivation` sends a derivation to the associated morphism. -/
theorem homEquivDerivation_symm_apply (S : CompleteLocalAlgCat Λ k) (V : Type u)
    [AddCommGroup V] [Module k V] [Module Λ V] [IsScalarTower Λ k V] [Module.Finite k V]
    (D : Derivation Λ S.carrier V) :
    (homEquivDerivation S V).symm D = derivationToHom S V D := sorry

/-- The derivation associated to a residue-compatible map `f : S ⟶ k[ε]`, given by
`D s = (f.hom s).snd`. -/
def dualNumberHomToDerivation (S : CompleteLocalAlgCat Λ k)
    (f : S ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.dualNumber Λ k)) :
    Derivation Λ S.carrier k where
  toFun s := (f.hom s).snd
  map_add' := sorry
  map_smul' := sorry
  map_one_eq_zero' := sorry
  leibniz' := sorry

/-- `dualNumberHomToDerivation f` evaluates as the infinitesimal component of `f`. -/
theorem dualNumberHomToDerivation_apply (S : CompleteLocalAlgCat Λ k)
    (f : S ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.dualNumber Λ k))
    (s : S.carrier) :
    dualNumberHomToDerivation S f s = (f.hom s).snd := sorry

/-- The `Ĉ_Λ`-morphism `S ⟶ k[ε]` associated to a derivation `D`, given by
`f s = inl (residueFieldHom S s) + inr (D s)`. -/
def dualNumberDerivationToHom (S : CompleteLocalAlgCat Λ k)
    (D : Derivation Λ S.carrier k) :
    S ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.dualNumber Λ k) where
  hom :=
    { toFun := fun s ↦ inl (residueFieldHom S s) + inr (D s)
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry
      commutes' := sorry }
  isLocalHom := sorry
  residue_compat := sorry

/-- `dualNumberDerivationToHom D` evaluates to the dual number with residue `q s` and
infinitesimal `D s`. -/
theorem dualNumberDerivationToHom_apply (S : CompleteLocalAlgCat Λ k)
    (D : Derivation Λ S.carrier k) (s : S.carrier) :
    (dualNumberDerivationToHom S D).hom s = inl (residueFieldHom S s) + inr (D s) := sorry

/-- Morphisms `S ⟶ k[ε]` in `Ĉ_Λ` are equivalent to `Λ`-derivations `S → k`. -/
def dualNumberHomEquivDerivation (S : CompleteLocalAlgCat Λ k) :
    (S ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.dualNumber Λ k)) ≃
      Derivation Λ S.carrier k :=
  Equiv.mk (dualNumberHomToDerivation S) (dualNumberDerivationToHom S) sorry sorry

/-- `dualNumberHomEquivDerivation` sends a morphism to the associated derivation. -/
theorem dualNumberHomEquivDerivation_apply (S : CompleteLocalAlgCat Λ k)
    (f : S ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.dualNumber Λ k)) :
    dualNumberHomEquivDerivation S f = dualNumberHomToDerivation S f := sorry

/-- The inverse of `dualNumberHomEquivDerivation` sends a derivation to the associated
morphism. -/
theorem dualNumberHomEquivDerivation_symm_apply (S : CompleteLocalAlgCat Λ k)
    (D : Derivation Λ S.carrier k) :
    (dualNumberHomEquivDerivation S).symm D = dualNumberDerivationToHom S D := sorry

end CompleteLocalAlgCat

namespace CategoryTheory.Functor

/-- Restricted coyoneda of `S` takes a unique value at the residue field. -/
instance instUnique_restrictedCoyoneda_residue (S : CompleteLocalAlgCat Λ k) :
    Unique ((CompleteLocalAlgCat.restrictedCoyoneda S).obj (ArtinianLocalAlgCat.residue Λ k)) where
  default := CompleteLocalAlgCat.residueHom S
  uniq := sorry

/-- Restricted coyoneda of `S` is a predeformation functor: its value at `k` is a
singleton. -/
instance instIsPredeformationFunctor_restrictedCoyoneda (S : CompleteLocalAlgCat Λ k) :
    IsPredeformationFunctor (CompleteLocalAlgCat.restrictedCoyoneda S) where
  unique_residue := ⟨inferInstance⟩

end CategoryTheory.Functor

namespace CategoryTheory.Functor.IsPredeformationFunctor

/-- The tangent space of `underline{S}|_{C_Λ}` is equivalent to `Derivation Λ S.carrier k`. -/
def tangentSpaceEquivDerivation (S : CompleteLocalAlgCat Λ k) :
    tangentSpace (CompleteLocalAlgCat.restrictedCoyoneda S) ≃ Derivation Λ S.carrier k :=
  CompleteLocalAlgCat.dualNumberHomEquivDerivation S

/-- `tangentSpaceEquivDerivation` is `dualNumberHomEquivDerivation` on the tangent space. -/
theorem tangentSpaceEquivDerivation_apply (S : CompleteLocalAlgCat Λ k)
    (f : tangentSpace (CompleteLocalAlgCat.restrictedCoyoneda S)) :
    tangentSpaceEquivDerivation S f = CompleteLocalAlgCat.dualNumberHomToDerivation S f := sorry

/-- The inverse of `tangentSpaceEquivDerivation` reconstructs the dual-number morphism. -/
theorem tangentSpaceEquivDerivation_symm_apply (S : CompleteLocalAlgCat Λ k)
    (D : Derivation Λ S.carrier k) :
    (tangentSpaceEquivDerivation S).symm D =
      CompleteLocalAlgCat.dualNumberDerivationToHom S D := sorry

/-- Additive group structure on `TF` transported from `Derivation Λ S.carrier k`. -/
instance instAddCommGroup_tangentSpace_restrictedCoyoneda (S : CompleteLocalAlgCat Λ k) :
    AddCommGroup (tangentSpace (CompleteLocalAlgCat.restrictedCoyoneda S)) :=
  Equiv.addCommGroup (tangentSpaceEquivDerivation S)

/-- `k`-module structure on `TF` transported along `tangentSpaceEquivDerivation`. -/
instance instModule_tangentSpace_restrictedCoyoneda (S : CompleteLocalAlgCat Λ k) :
    Module k (tangentSpace (CompleteLocalAlgCat.restrictedCoyoneda S)) where
  smul c x := (tangentSpaceEquivDerivation S).symm (c • tangentSpaceEquivDerivation S x)
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- Scalar multiplication on `TF` is transport of the `k`-action on derivations. -/
theorem smul_tangentSpace (S : CompleteLocalAlgCat Λ k) (c : k)
    (x : tangentSpace (CompleteLocalAlgCat.restrictedCoyoneda S)) :
    c • x = (tangentSpaceEquivDerivation S).symm (c • tangentSpaceEquivDerivation S x) :=
  sorry

end CategoryTheory.Functor.IsPredeformationFunctor

end
