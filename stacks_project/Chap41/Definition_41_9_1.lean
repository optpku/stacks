/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.FaithfullyFlat
import StacksCheckRecall

@[expose] public section

open CategoryTheory MonoidalCategory

universe u

variable {R S : Type u} [CommRing R] [CommRing S]
variable (M : ModuleCat.{u} R) (f : R →+* S)

/- Definition 41.9.1 (1): an `R`-module `M` is flat exactly when the functor
`X ↦ X ⊗[R] M` is exact. -/
@[stacks 0251]
#check (Module.Flat.iff_exactFunctor_tensorRight M :
  Module.Flat R M ↔
    exactFunctor (ModuleCat.{u} R) (ModuleCat.{u} R) (tensorRight M))

/- Definition 41.9.1 (2): an `R`-module `M` is faithfully flat exactly when the functor
`X ↦ X ⊗[R] M` is exact and faithful. -/
@[stacks 0251]
#check (Module.FaithfullyFlat.iff_exactFunctor_and_faithful_tensorRight M :
  Module.FaithfullyFlat R M ↔
    exactFunctor (ModuleCat.{u} R) (ModuleCat.{u} R) (tensorRight M) ∧
      (tensorRight M).Faithful)

/- Definition 41.9.1 (3): a homomorphism `f : R →+* S` is flat exactly when extension of
scalars along `f` is exact. -/
@[stacks 0251]
#check (ModuleCat.extendScalars_exact_iff_flat f :
  exactFunctor (ModuleCat.{u} R) (ModuleCat.{u} S)
      (ModuleCat.extendScalars.{u, u, u} f) ↔
    f.Flat)

/- Definition 41.9.1 (4): a homomorphism `f : R →+* S` is faithfully flat exactly when
extension of scalars along `f` is exact and faithful. -/
@[stacks 0251]
#check (ModuleCat.ExtendScalars.faithfullyFlat_iff_exact_and_faithful f :
  f.FaithfullyFlat ↔
    exactFunctor (ModuleCat.{u} R) (ModuleCat.{u} S)
        (ModuleCat.extendScalars.{u, u, u} f) ∧
      (ModuleCat.extendScalars.{u, u, u} f).Faithful)
