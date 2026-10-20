module

public import ReasLib.Algebra.Category.ModuleCat.DualNumber.Ext
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped DualNumber

universe u

/- Exercise 111.11.3: if `k` is a field, then `R = k[ε]` is Noetherian, the residue
module `M = N = DualNumber.residueModule k` is a finite `R`-module, and
`Ext i` of this pair is a nontrivial abelian group for every `i : ℕ`. -/
@[stacks 0CRE] #check
  (DualNumber.residueExt_nontrivial :
    ∀ (k : Type u) [Field k] (i : ℕ),
      Nontrivial (Abelian.Ext
        (DualNumber.residueModule k) (DualNumber.residueModule k) i))

@[stacks 0CRE] #check fun (k : Type u) [Field k] ↦
  (inferInstance : IsNoetherianRing k[ε])

@[stacks 0CRE] #check fun (k : Type u) [Field k] ↦
  (inferInstance : Module.Finite k[ε] (k[ε] ⧸ DualNumber.epsIdeal k))
