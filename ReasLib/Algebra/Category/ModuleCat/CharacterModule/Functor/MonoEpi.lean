/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import ReasLib.Algebra.Category.ModuleCat.CharacterModule.Functor
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Monomorphisms and epimorphisms under character duality

Character duality exchanges injective and surjective module maps. This leaf
packages the resulting `Mono`/`Epi` criteria and installs the coherent
instances for the canonical bundled maps.
-/

open CategoryTheory

universe u v

namespace CharacterModule

section Commutative

variable (R : Type u) [CommRing R]
variable {M N : ModuleCat.{v} R}

/-- A character-dual map is mono exactly when the original map is epi. -/
@[stacks 01DA "character duality exchanges epimorphisms and monomorphisms"]
theorem mono_dualMap_iff_epi (f : M ⟶ N) :
    Mono (dualMap R f) ↔ Epi f := sorry
/- Proof strategy: combine `ModuleCat.mono_iff_injective`,
`ModuleCat.epi_iff_surjective`, and
`CharacterModule.dual_injective_iff_surjective`. -/

/-- A character-dual map is epi exactly when the original map is mono. -/
@[stacks 01DA "character duality exchanges monomorphisms and epimorphisms"]
theorem epi_dualMap_iff_mono (f : M ⟶ N) :
    Epi (dualMap R f) ↔ Mono f := sorry
/- Proof strategy: combine `ModuleCat.epi_iff_surjective`,
`ModuleCat.mono_iff_injective`, and
`CharacterModule.dual_surjective_iff_injective`. -/

/-- Dualizing an epimorphism canonically gives a monomorphism. -/
@[stacks 01DA "character duality mono instance"]
instance dualMap_mono (f : M ⟶ N) [Epi f] : Mono (dualMap R f) := sorry
/- Proof strategy: apply `mono_dualMap_iff_epi`. -/

/-- Dualizing a monomorphism canonically gives an epimorphism. -/
@[stacks 01DA "character duality epi instance"]
instance dualMap_epi (f : M ⟶ N) [Mono f] : Epi (dualMap R f) := sorry
/- Proof strategy: apply `epi_dualMap_iff_mono`. -/

/-- The character-module functor sends opposite epimorphisms to
monomorphisms. -/
@[stacks 01DA "character functor mono instance"]
instance functor_map_op_mono (f : M ⟶ N) [Epi f] :
    Mono ((functor R).map f.op) := sorry
/- Proof strategy: rewrite with `functor_map_op` and infer
`dualMap_mono`. -/

/-- The character-module functor sends opposite monomorphisms to
epimorphisms. -/
@[stacks 01DA "character functor epi instance"]
instance functor_map_op_epi (f : M ⟶ N) [Mono f] :
    Epi ((functor R).map f.op) := sorry
/- Proof strategy: rewrite with `functor_map_op` and infer
`dualMap_epi`. -/

end Commutative

section Opposite

variable (R : Type u) [Ring R]
variable {M N : ModuleCat.{v} R}

/-- An opposite-linear character-dual map is mono exactly when the original
map is epi. -/
@[stacks 01DA "opposite character duality mono criterion"]
theorem mono_dualOppositeMap_iff_epi (f : M ⟶ N) :
    Mono (dualOppositeMap R f) ↔ Epi f := sorry
/- Proof strategy: use the ModuleCat mono/epi criteria and the underlying
additive-character injectivity criterion. -/

/-- An opposite-linear character-dual map is epi exactly when the original
map is mono. -/
@[stacks 01DA "opposite character duality epi criterion"]
theorem epi_dualOppositeMap_iff_mono (f : M ⟶ N) :
    Epi (dualOppositeMap R f) ↔ Mono f := sorry
/- Proof strategy: use the ModuleCat mono/epi criteria and the underlying
additive-character surjectivity criterion. -/

/-- Opposite-linear dualization sends epimorphisms to monomorphisms. -/
@[stacks 01DA "opposite character duality mono instance"]
instance dualOppositeMap_mono (f : M ⟶ N) [Epi f] :
    Mono (dualOppositeMap R f) := sorry
/- Proof strategy: apply `mono_dualOppositeMap_iff_epi`. -/

/-- Opposite-linear dualization sends monomorphisms to epimorphisms. -/
@[stacks 01DA "opposite character duality epi instance"]
instance dualOppositeMap_epi (f : M ⟶ N) [Mono f] :
    Epi (dualOppositeMap R f) := sorry
/- Proof strategy: apply `epi_dualOppositeMap_iff_mono`. -/

/-- The opposite-ring character functor sends opposite epimorphisms to
monomorphisms. -/
@[stacks 01DA "opposite character functor mono instance"]
instance opFunctor_map_op_mono (f : M ⟶ N) [Epi f] :
    Mono ((opFunctor R).map f.op) := sorry
/- Proof strategy: rewrite with `opFunctor_map_op` and infer
`dualOppositeMap_mono`. -/

/-- The opposite-ring character functor sends opposite monomorphisms to
epimorphisms. -/
@[stacks 01DA "opposite character functor epi instance"]
instance opFunctor_map_op_epi (f : M ⟶ N) [Mono f] :
    Epi ((opFunctor R).map f.op) := sorry
/- Proof strategy: rewrite with `opFunctor_map_op` and infer
`dualOppositeMap_epi`. -/

end Opposite

/-- Character-module duality reflects monomorphisms. -/
instance instFunctorReflectsMonomorphisms (R : Type u) [CommRing R] :
    (functor R : (ModuleCat.{v} R)ᵒᵖ ⥤ ModuleCat.{v} R).ReflectsMonomorphisms := sorry

/-- Character-module duality reflects epimorphisms. -/
instance instFunctorReflectsEpimorphisms (R : Type u) [CommRing R] :
    (functor R : (ModuleCat.{v} R)ᵒᵖ ⥤ ModuleCat.{v} R).ReflectsEpimorphisms := sorry

end CharacterModule
