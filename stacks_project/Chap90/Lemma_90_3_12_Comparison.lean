/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Submodule.LinearMap
public import ReasLib.RingTheory.Kaehler.BaseChange
public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal
public import stacks_project.Chap90.«90_3_10_2_ResidueAlgebra»
public import stacks_project.Chap90.«90_3_10_3_Comparison»

/-!
# Hom-induced Kähler comparison maps in `C_Λ`

A morphism `f : B ⟶ A` in `ArtinianLocalAlgCat Λ k` induces the `k`-linear
Kähler base-change map `k ⊗[B.carrier] Ω[B.carrier⁄Λ] → k ⊗[A.carrier] Ω[A.carrier⁄Λ]`
and its restriction `conormalRange B → conormalRange A` on images of the
extended conormal maps `d_B` and `d_A`.
-/

@[expose] public section

open CategoryTheory KaehlerDifferential
open scoped TensorProduct

universe u

namespace ArtinianLocalAlgCat

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

noncomputable section

/-- The `B.carrier`-algebra structure on `A.carrier` induced by a morphism in
`ArtinianLocalAlgCat`. -/
@[reducible] def algebraOfHom {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    Algebra B.carrier A.carrier :=
  f.hom.toRingHom.toAlgebra

/-- `algebraOfHom` is the algebra structure of the underlying ring homomorphism. -/
theorem algebraOfHom_eq {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    algebraOfHom f = f.hom.toRingHom.toAlgebra := sorry

/-- The image of the extended conormal map `d_A`, as a `k`-submodule of
`k ⊗[A.carrier] Ω[A.carrier⁄Λ]`. -/
abbrev conormalRange (A : ArtinianLocalAlgCat Λ k) :
    Submodule k (k ⊗[A.carrier] Ω[A.carrier⁄Λ]) :=
  LinearMap.range (kerCotangentToTensor_extend Λ A.carrier k A.algebraMap_surjective)

/-- Membership in `conormalRange A` is being in the image of the extended conormal
map `d_A`. -/
theorem mem_conormalRange {A : ArtinianLocalAlgCat Λ k}
    {x : k ⊗[A.carrier] Ω[A.carrier⁄Λ]} :
    x ∈ conormalRange A ↔
      ∃ y, kerCotangentToTensor_extend Λ A.carrier k A.algebraMap_surjective y = x :=
  sorry

namespace Hom

/-- The `k`-linear Kähler base-change map induced by a morphism in `C_Λ`. -/
def kaehlerTensorMap {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    k ⊗[B.carrier] Ω[B.carrier⁄Λ] →ₗ[k] k ⊗[A.carrier] Ω[A.carrier⁄Λ] :=
  -- Local instance justification (noncanonical choice): Algebra of A.carrier over B.carrier is induced by this morphism, not a unique ambient Algebra on the pair of carriers.
  letI := algebraOfHom f
  -- Local instance justification (noncanonical choice): the tower Λ → B.carrier → A.carrier is determined by this morphism.
  letI : IsScalarTower Λ B.carrier A.carrier := sorry
  -- Local instance justification (noncanonical choice): the tower B.carrier → A.carrier → k is determined by this morphism together with the residue identifications.
  letI : IsScalarTower B.carrier A.carrier k := sorry
  tensorMapBaseChange Λ B.carrier A.carrier k

/-- `kaehlerTensorMap` is `k`-linear on pure tensors. -/
theorem kaehlerTensorMap_tmul {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A)
    (t : k) (x : Ω[B.carrier⁄Λ]) :
    kaehlerTensorMap f (t ⊗ₜ[B.carrier] x) =
      t • kaehlerTensorMap f (1 ⊗ₜ[B.carrier] x) :=
  sorry

/-- The Kähler base-change map of `f` sends `conormalRange B` into `conormalRange A`. -/
theorem kaehlerTensorMap_mapsTo_conormalRange {B A : ArtinianLocalAlgCat Λ k}
    (f : B ⟶ A) :
    ∀ x ∈ conormalRange B, kaehlerTensorMap f x ∈ conormalRange A :=
  sorry

/-- The restriction of `kaehlerTensorMap f` to images of the extended conormal maps,
i.e. the source map `Im(d_B) → Im(d_A)`. -/
def conormalRangeMap {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    conormalRange B →ₗ[k] conormalRange A :=
  (kaehlerTensorMap f).restrict (kaehlerTensorMap_mapsTo_conormalRange f)

/-- `conormalRangeMap` applies as `kaehlerTensorMap` on underlying tensors. -/
theorem conormalRangeMap_apply {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A)
    (x : conormalRange B) :
    (conormalRangeMap f x : k ⊗[A.carrier] Ω[A.carrier⁄Λ]) =
      kaehlerTensorMap f (x : k ⊗[B.carrier] Ω[B.carrier⁄Λ]) :=
  sorry

end Hom

end

end ArtinianLocalAlgCat
