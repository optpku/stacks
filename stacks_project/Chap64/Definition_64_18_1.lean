/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 64.18.1 (1): on a Noetherian scheme X, a ℤ_[ℓ]-sheaf (also called an
ℓ-adic sheaf) is an inverse system {F_n}_{n ≥ 1} of constructible ZMod (ℓ^n)-modules
on X étale whose transitions F_{n+1} ⟶ F_n induce
F_{n+1} ⊗_{ZMod (ℓ^{n+1})} ZMod (ℓ^n) ≅ F_n. -/
@[stacks 03UM] #check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf :
  ∀ (X : Scheme.{u}) (ℓ : ℕ) [Fact (Nat.Prime ℓ)] [IsNoetherian X]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ (Y : Scheme.{u}) (V : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}], Type (u + 1))

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [IsNoetherian X]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

/- Definition 64.18.1 (2): a ℤ_[ℓ]-sheaf is lisse when each stage is locally constant. -/
@[stacks 03UM] #check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.IsLisse :
  AlgebraicGeometry.Scheme.Etale.ZEllSheaf X ℓ → Prop)

/- Definition 64.18.1 (3): a morphism of ℤ_[ℓ]-sheaves is a morphism of inverse systems. -/
@[stacks 03UM] #check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.Hom :
  AlgebraicGeometry.Scheme.Etale.ZEllSheaf X ℓ →
    AlgebraicGeometry.Scheme.Etale.ZEllSheaf X ℓ → Type (u + 1))
