/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Diagonal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale

/-! # Self fibre powers and pairwise diagonals -/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Recursive data for the `n`-fold fibre product of `f : U ⟶ X` over `X`, together with
its structure morphism to `X`. -/
noncomputable def selfFibrePowerData {U X : AlgebraicSpace S} (f : U ⟶ X) :
    ℕ → (W : AlgebraicSpace S) × (W ⟶ X)
  | 0 => ⟨X, 𝟙 X⟩
  | n + 1 =>
    ⟨pullback (selfFibrePowerData f n).2 f,
      pullback.fst (selfFibrePowerData f n).2 f ≫ (selfFibrePowerData f n).2⟩

/-- The `n`-fold fibre product of `f : U ⟶ X` over `X`. The `0`-fold product is `X`
and the successor is the binary pullback of the previous structure morphism along `f`. -/
noncomputable def selfFibrePower {U X : AlgebraicSpace S} (f : U ⟶ X) (n : ℕ) :
    AlgebraicSpace S :=
  (selfFibrePowerData f n).1

/-- The structure morphism of the `n`-fold fibre product of `f` over `X`. -/
noncomputable def selfFibrePowerToBase {U X : AlgebraicSpace S} (f : U ⟶ X) (n : ℕ) :
    selfFibrePower f n ⟶ X :=
  (selfFibrePowerData f n).2

/-- The `0`-fold fibre product of `f` is the base `X`. -/
theorem selfFibrePower_zero {U X : AlgebraicSpace S} (f : U ⟶ X) :
    selfFibrePower f 0 = X :=
  rfl

/-- The successor fibre product is the binary pullback of the previous structure morphism
along `f`. -/
theorem selfFibrePower_succ {U X : AlgebraicSpace S} (f : U ⟶ X) (n : ℕ) :
    selfFibrePower f (n + 1) = pullback (selfFibrePowerToBase f n) f :=
  rfl

/-- The structure morphism of the `0`-fold fibre product is the identity of `X`. -/
theorem selfFibrePowerToBase_zero {U X : AlgebraicSpace S} (f : U ⟶ X) :
    selfFibrePowerToBase f 0 = 𝟙 X :=
  rfl

/-- The structure morphism of a successor fibre product is `pullback.fst ≫` the previous
structure morphism. -/
theorem selfFibrePowerToBase_succ {U X : AlgebraicSpace S} (f : U ⟶ X) (n : ℕ) :
    selfFibrePowerToBase f (n + 1) =
      pullback.fst (selfFibrePowerToBase f n) f ≫ selfFibrePowerToBase f n :=
  rfl

/-- The `i`-th projection of the `n`-fold fibre product of `f` onto `U`. -/
noncomputable def selfFibrePowerπ {U X : AlgebraicSpace S} (f : U ⟶ X) :
    (n : ℕ) → Fin n → (selfFibrePower f n ⟶ U)
  | 0, i => Fin.elim0 i
  | n + 1, i =>
    if h : i.val = n then
      pullback.snd (selfFibrePowerToBase f n) f
    else
      pullback.fst (selfFibrePowerToBase f n) f ≫
        selfFibrePowerπ f n ⟨i.val, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ i.isLt) h⟩

/-- Each projection of the `n`-fold fibre product lies over `X` via `f`. -/
theorem selfFibrePowerπ_comp_toBase {U X : AlgebraicSpace S} (f : U ⟶ X) (n : ℕ)
    (i : Fin n) : selfFibrePowerπ f n i ≫ f = selfFibrePowerToBase f n :=
  sorry

/-- The universal map into a fibre power induced by morphisms with a common base map. -/
noncomputable def selfFibrePowerLift {U X W : AlgebraicSpace S} (f : U ⟶ X) (g : W ⟶ X) :
    (n : ℕ) → (πs : Fin n → (W ⟶ U)) → (∀ i, πs i ≫ f = g) →
      (W ⟶ selfFibrePower f n)
  | 0, _, _ => g
  | n + 1, πs, hπ =>
    pullback.lift
      (selfFibrePowerLift f g n (fun i => πs i.castSucc) (fun i => hπ i.castSucc))
      (πs (Fin.last n)) sorry

/-- The mediating morphism recovers the given projections. -/
theorem selfFibrePowerLift_π {U X W : AlgebraicSpace S} (f : U ⟶ X) (g : W ⟶ X) (n : ℕ)
    (πs : Fin n → (W ⟶ U)) (hπ : ∀ i, πs i ≫ f = g) (i : Fin n) :
    selfFibrePowerLift f g n πs hπ ≫ selfFibrePowerπ f n i = πs i :=
  sorry

/-- The universal map into a fibre power recovers the prescribed base map. -/
theorem selfFibrePowerLift_comp_toBase {U X W : AlgebraicSpace S} (f : U ⟶ X)
    (g : W ⟶ X) (n : ℕ) (πs : Fin n → (W ⟶ U)) (hπ : ∀ i, πs i ≫ f = g) :
    selfFibrePowerLift f g n πs hπ ≫ selfFibrePowerToBase f n = g :=
  sorry

/-- The permutation automorphism of the `n`-fold fibre product of `f` induced by
`σ : Equiv.Perm (Fin n)`, uniquely determined by permuting the projections. -/
noncomputable def selfFibrePowerPerm {U X : AlgebraicSpace S} (f : U ⟶ X) (n : ℕ) :
    Equiv.Perm (Fin n) →* Aut (selfFibrePower f n) where
  toFun σ :=
    { hom := selfFibrePowerLift f (selfFibrePowerToBase f n) n
        (fun i => selfFibrePowerπ f n (σ.symm i))
        (fun i => selfFibrePowerπ_comp_toBase f n (σ.symm i))
      inv := selfFibrePowerLift f (selfFibrePowerToBase f n) n
        (fun i => selfFibrePowerπ f n (σ i))
        (fun i => selfFibrePowerπ_comp_toBase f n (σ i))
      hom_inv_id := sorry
      inv_hom_id := sorry }
  map_one' := sorry
  map_mul' := sorry

/-- Permuting factors sends the `i`-th projection to the `σ.symm i`-th projection. -/
theorem selfFibrePowerPerm_π {U X : AlgebraicSpace S} (f : U ⟶ X) {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (selfFibrePowerPerm f n σ).hom ≫ selfFibrePowerπ f n i =
      selfFibrePowerπ f n (σ.symm i) :=
  sorry

/-- The comparison morphism from the `n`-fold fibre product to `U ×_X U` determined by
the pair of projections `π_i` and `π_j`. -/
noncomputable def pairwiseComparison {U X : AlgebraicSpace S} (f : U ⟶ X) {n : ℕ}
    (i j : Fin n) : selfFibrePower f n ⟶ pullback f f :=
  pullback.lift (selfFibrePowerπ f n i) (selfFibrePowerπ f n j)
    ((selfFibrePowerπ_comp_toBase f n i).trans (selfFibrePowerπ_comp_toBase f n j).symm)

/-- The pairwise diagonal `Δ_{ij}` in the `n`-fold fibre product of `f`, as the pullback
of the relative diagonal along the comparison morphism of `π_i` and `π_j`. -/
noncomputable def pairwiseDiagonal {U X : AlgebraicSpace S} (f : U ⟶ X) {n : ℕ}
    (i j : Fin n) : AlgebraicSpace S :=
  pullback (pairwiseComparison f i j) (pullback.diagonal f)

/-- The inclusion of the pairwise diagonal `Δ_{ij}` into the `n`-fold fibre product. -/
noncomputable def pairwiseDiagonalι {U X : AlgebraicSpace S} (f : U ⟶ X) {n : ℕ}
    (i j : Fin n) : pairwiseDiagonal f i j ⟶ selfFibrePower f n :=
  pullback.fst (pairwiseComparison f i j) (pullback.diagonal f)

/-- The inclusion of a pairwise diagonal is the first projection of the pullback of the
relative diagonal. -/
theorem pairwiseDiagonalι_eq {U X : AlgebraicSpace S} (f : U ⟶ X) {n : ℕ} (i j : Fin n) :
    pairwiseDiagonalι f i j =
      pullback.fst (pairwiseComparison f i j) (pullback.diagonal f) :=
  rfl

/-- If `f` is separated, each pairwise diagonal inclusion is a closed immersion. -/
instance instIsClosedImmersion_pairwiseDiagonalι {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Separated f] {n : ℕ} (i j : Fin n) :
    IsClosedImmersion (pairwiseDiagonalι f i j) :=
  sorry

/-- If `f` is étale, the structure morphism of each self fibre power is étale. -/
instance instEtale_selfFibrePowerToBase {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    (n : ℕ) : Etale (selfFibrePowerToBase f n) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
