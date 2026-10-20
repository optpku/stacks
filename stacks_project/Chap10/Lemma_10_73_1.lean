module

public import ReasLib.Algebra.Category.ModuleCat.Ext.FlatBaseChange
import StacksCheckRecall

/-!
# Lemma 10.73.1

@stack 087N
-/

@[expose] public section

noncomputable section

open CategoryTheory Abelian

universe u

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (M : ModuleCat.{u} R) (N : ModuleCat.{u} S)
variable (hflat : (algebraMap R S).Flat) (i : ℕ)

/- Lemma 10.73.1: for a flat ring map `R → S`, the natural map
`Ext^i_S(S ⊗_R M, N) → Ext^i_R(M, N|_R)` is an isomorphism. -/
@[stacks 087N]
#check (ModuleCat.Ext.FlatBaseChange.equiv (algebraMap R S) M N hflat i :
  Ext ((ModuleCat.extendScalars (algebraMap R S)).obj M) N i ≃+
    Ext M ((ModuleCat.restrictScalars (algebraMap R S)).obj N) i)

#check (ModuleCat.Ext.FlatBaseChange.comparison (algebraMap R S) M N i :
  Ext ((ModuleCat.extendScalars (algebraMap R S)).obj M) N i →+
    Ext M ((ModuleCat.restrictScalars (algebraMap R S)).obj N) i)

#check (ModuleCat.Ext.FlatBaseChange.adjoint (algebraMap R S) M N hflat i :
  Ext M ((ModuleCat.restrictScalars (algebraMap R S)).obj N) i →+
    Ext ((ModuleCat.extendScalars (algebraMap R S)).obj M) N i)

end
