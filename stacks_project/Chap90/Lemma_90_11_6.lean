module

public import stacks_project.Chap90.Lemma_90_11_6_Tensor

/-!
# Lemma 90.11.6

A `K`-linear functor `L : FGModuleCat K ⥤ ModuleCat K` is isomorphic to
left tensoring by `L(K)`.
-/

@[expose] public section

open CategoryTheory

universe u

variable {K : Type u} [Field K]

namespace FGModuleCat

/-- Lemma 90.11.6: a `K`-linear functor `L : FGModuleCat K ⥤ ModuleCat K` is
isomorphic to the functor `L(K) ⊗[K] -`, via the canonical comparison
`tensorNatTrans L : tensoringLeft (L.obj (of K K)) ⟶ L`. -/
@[stacks 06I8]
instance isIso_tensorNatTrans (L : FGModuleCat.{u} K ⥤ ModuleCat.{u} K) [L.ModuleLinear K] :
    IsIso (tensorNatTrans L) := sorry

end FGModuleCat
