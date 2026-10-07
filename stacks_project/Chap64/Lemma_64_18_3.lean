module

public import stacks_project.Chap64.Lemma_64_18_3_Category
public import stacks_project.Chap64.Lemma_64_18_3_Kernel
public import stacks_project.Chap64.Lemma_64_18_3_Instances
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory

universe u

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [IsNoetherian X]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

/- Lemma 64.18.3: the category of ℤ_[ℓ]-sheaves on a Noetherian scheme X is abelian. -/
@[stacks 03UO] #check (ZEllSheaf.instAbelian : Abelian (ZEllSheaf X ℓ))
