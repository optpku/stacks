/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Prorepresentable.Endomorphism
import StacksCheckRecall

/-!
# Endomorphisms of prorepresentable functors with invertible differential

If `U : ArtinianLocalAlgCat Λ k ⥤ Type u` is prorepresentable, an endomorphism
whose dual-number component is bijective is itself an isomorphism.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Lemma 90.27.3: if `U : ArtinianLocalAlgCat Λ k ⥤ Type u` is prorepresentable and
`φ : U ⟶ U` is a morphism such that `dφ : TU → TU` is an isomorphism, then `φ` is an
isomorphism. Here `TU` is `U.obj (ArtinianLocalAlgCat.dualNumber Λ k)` and `dφ` is the
component `φ.app (ArtinianLocalAlgCat.dualNumber Λ k)`. -/
@[stacks 06KP] #check (CategoryTheory.Functor.isIso_of_bijective_tangentSpace :
  ∀ {U : ArtinianLocalAlgCat Λ k ⥤ Type u} [CategoryTheory.Functor.IsProrepresentable U]
    (φ : U ⟶ U),
    Function.Bijective (φ.app (ArtinianLocalAlgCat.dualNumber Λ k)) → IsIso φ)
