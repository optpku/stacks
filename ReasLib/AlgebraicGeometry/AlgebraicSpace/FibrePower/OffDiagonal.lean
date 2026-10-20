module

public import Mathlib.Algebra.Group.ULift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FibrePower
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.FiniteIntersection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.ComplementLift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.OpenImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FreeQuotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

/-! # Off-diagonal fibre products and their permutation actions -/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The open complement of the pairwise diagonal `Δ_{ij}` inside the `n`-fold fibre
product of `f`. -/
noncomputable def pairwiseDiagonalComplement {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Separated f] {n : ℕ} (i j : Fin n) : OpenSubspace (selfFibrePower f n) :=
  closedImmersionComplementSubspace (pairwiseDiagonalι f i j)

/-- Pairwise diagonal complements, reindexed by strictly ordered pairs `j < i`. -/
noncomputable def pairwiseDiagonalComplementFamily {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Separated f] (n : ℕ) (i : Fin n) (j : Fin i.val) :
    OpenSubspace (selfFibrePower f n) :=
  pairwiseDiagonalComplement f ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩ i

/-- The open subspace of the `n`-fold fibre product of `f` obtained by deleting all
pairwise diagonals. -/
noncomputable def offDiagonalSubspace {U X : AlgebraicSpace S} (f : U ⟶ X) [Separated f]
    (n : ℕ) : OpenSubspace (selfFibrePower f n) :=
  OpenSubspace.infFamily n (pairwiseDiagonalComplementFamily f n)

/-- The algebraic space `W` obtained from the `n`-fold fibre product of `f` by deleting
all pairwise diagonals. -/
noncomputable def offDiagonal {U X : AlgebraicSpace S} (f : U ⟶ X) [Separated f] (n : ℕ) :
    AlgebraicSpace S :=
  (offDiagonalSubspace f n).X

/-- The open inclusion of the off-diagonal locus into the `n`-fold fibre product. -/
noncomputable def offDiagonalι {U X : AlgebraicSpace S} (f : U ⟶ X) [Separated f] (n : ℕ) :
    offDiagonal f n ⟶ selfFibrePower f n :=
  (offDiagonalSubspace f n).ι

/-- The structure morphism `W ⟶ X` of the off-diagonal locus. -/
noncomputable def offDiagonalToBase {U X : AlgebraicSpace S} (f : U ⟶ X) [Separated f]
    (n : ℕ) : offDiagonal f n ⟶ X :=
  offDiagonalι f n ≫ selfFibrePowerToBase f n

/-- The off-diagonal inclusion is the inclusion of the folded open subspace. -/
theorem offDiagonalι_eq {U X : AlgebraicSpace S} (f : U ⟶ X) [Separated f] (n : ℕ) :
    offDiagonalι f n = (offDiagonalSubspace f n).ι :=
  rfl

/-- The structure morphism of the off-diagonal locus is the composite of the open
inclusion with the fibre-power structure morphism. -/
theorem offDiagonalToBase_eq {U X : AlgebraicSpace S} (f : U ⟶ X) [Separated f] (n : ℕ) :
    offDiagonalToBase f n = offDiagonalι f n ≫ selfFibrePowerToBase f n :=
  rfl

/-- The off-diagonal inclusion is an open immersion. -/
instance instIsOpenImmersion_offDiagonalι {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Separated f] (n : ℕ) : IsOpenImmersion (offDiagonalι f n) :=
  (offDiagonalSubspace f n).isOpenImmersion

/-- If `f` is étale and separated, the structure morphism of the off-diagonal locus is
étale. -/
instance instEtale_offDiagonalToBase {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    [Separated f] (n : ℕ) : Etale (offDiagonalToBase f n) :=
  sorry

/-- The off-diagonal inclusion is étale. -/
instance instEtale_offDiagonalι {U X : AlgebraicSpace S} (f : U ⟶ X) [Separated f]
    (n : ℕ) : Etale (offDiagonalι f n) :=
  Etale.ofIsOpenImmersion

/-- If `f` is étale and separated, the off-diagonal inclusion is a closed immersion. -/
public instance instIsClosedImmersion_offDiagonalι {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Separated f] (n : ℕ) : IsClosedImmersion (offDiagonalι f n) :=
  sorry

/-- A map into the `n`-fold fibre product misses every pairwise diagonal. -/
def missesPairwiseDiagonals {T U X : AlgebraicSpace S} (f : U ⟶ X) [Separated f]
    {n : ℕ} (h : T ⟶ selfFibrePower f n) : Prop :=
  ∀ (i : Fin n) (j : Fin i.val) (V : (Over S)ᵒᵖ) (t : T.functorOfPoints.obj V),
    missesClosedImage (pairwiseDiagonalι f ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩ i)
      (h.app V t)

/-- Missing pairwise diagonals is the pointwise missing-closed-image condition on every
strictly ordered pair. -/
theorem missesPairwiseDiagonals_iff {T U X : AlgebraicSpace S} (f : U ⟶ X)
    [Separated f] {n : ℕ} (h : T ⟶ selfFibrePower f n) :
    missesPairwiseDiagonals f h ↔
      ∀ (i : Fin n) (j : Fin i.val) (V : (Over S)ᵒᵖ) (t : T.functorOfPoints.obj V),
        missesClosedImage (pairwiseDiagonalι f ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩ i)
          (h.app V t) :=
  Iff.rfl

/-- A map into the `n`-fold fibre product that misses every pairwise diagonal lifts to
the off-diagonal locus. -/
noncomputable def offDiagonalLift {T U X : AlgebraicSpace S} (f : U ⟶ X) [Separated f]
    (n : ℕ) (h : T ⟶ selfFibrePower f n) (h_miss : missesPairwiseDiagonals f h) :
    T ⟶ offDiagonal f n :=
  OpenSubspace.infFamilyLift n (pairwiseDiagonalComplementFamily f n) h (fun i j =>
    closedImmersionComplementLift
      (pairwiseDiagonalι f ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩ i) h fun V t =>
      h_miss i j V t)
    (fun i j => closedImmersionComplementLift_comp
      (pairwiseDiagonalι f ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩ i) h
      (fun V t => h_miss i j V t))

/-- The lift to the off-diagonal locus composes to the original map into the fibre
product. -/
theorem offDiagonalLift_comp {T U X : AlgebraicSpace S} (f : U ⟶ X) [Separated f]
    (n : ℕ) (h : T ⟶ selfFibrePower f n) (h_miss : missesPairwiseDiagonals f h) :
    offDiagonalLift f n h h_miss ≫ offDiagonalι f n = h :=
  sorry

/-- Permuting the factors of the fibre product preserves the off-diagonal locus. -/
theorem offDiagonalPerm_missesPairwiseDiagonals {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Separated f] (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    missesPairwiseDiagonals f (offDiagonalι f n ≫ (selfFibrePowerPerm f n σ).hom) :=
  sorry

/-- The permutation automorphism of the off-diagonal locus induced by permuting the
factors of the ambient fibre product. The inverse is the same mediating morphism at
`σ⁻¹`. -/
noncomputable def offDiagonalPerm {U X : AlgebraicSpace S} (f : U ⟶ X) [Separated f]
    (n : ℕ) : Equiv.Perm (Fin n) →* Aut (offDiagonal f n) where
  toFun σ :=
    { hom :=
        offDiagonalLift f n (offDiagonalι f n ≫ (selfFibrePowerPerm f n σ).hom)
          (offDiagonalPerm_missesPairwiseDiagonals f n σ)
      inv :=
        offDiagonalLift f n (offDiagonalι f n ≫ (selfFibrePowerPerm f n σ⁻¹).hom)
          (offDiagonalPerm_missesPairwiseDiagonals f n σ⁻¹)
      hom_inv_id := sorry
      inv_hom_id := sorry }
  map_one' := sorry
  map_mul' := sorry

/-- The permutation action on the off-diagonal locus lies over `X`. -/
theorem offDiagonalPerm_comp_toBase {U X : AlgebraicSpace S} (f : U ⟶ X) [Separated f]
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (offDiagonalPerm f n σ).hom ≫ offDiagonalToBase f n = offDiagonalToBase f n :=
  sorry

/-- The off-diagonal permutation action, with `S_n` lifted to the universe of `S`. -/
noncomputable def offDiagonalPermLift {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Separated f] (n : ℕ) :
    ULift.{u} (Equiv.Perm (Fin n)) →* Aut (offDiagonal f n) :=
  (offDiagonalPerm f n).comp
    (MulEquiv.ulift (α := Equiv.Perm (Fin n))).toMonoidHom

/-- `offDiagonalPermLift` evaluates as `offDiagonalPerm` on the underlying permutation. -/
theorem offDiagonalPermLift_apply {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Separated f] (n : ℕ) (σ : ULift.{u} (Equiv.Perm (Fin n))) :
    offDiagonalPermLift f n σ = offDiagonalPerm f n σ.down :=
  rfl

/-- Automorphisms coming from the permutation action on the off-diagonal locus are
étale. -/
instance instEtale_offDiagonalPerm {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    [Separated f] (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Etale ((offDiagonalPerm f n σ).hom) :=
  sorry

/-- The one-fold off-diagonal fibre product is isomorphic to its domain. -/
noncomputable def offDiagonal_one {U X : AlgebraicSpace S} (f : U ⟶ X) [Separated f] :
    offDiagonal f 1 ≅ U where
  hom := offDiagonalι f 1 ≫ pullback.snd (selfFibrePowerToBase f 0) f
  inv := offDiagonalLift f 1 (pullback.lift f (𝟙 U) sorry) sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The permutation action on the off-diagonal fibre product of a surjective étale
separated morphism is free. -/
instance instIsFree_offDiagonalPerm {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    [Surjective f] [Separated f] (p : ℕ) :
    IsFree (offDiagonalPermLift f (p + 1)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
