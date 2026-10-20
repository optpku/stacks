/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Differential

/-!
# Differential of a formal object

Compatibility checks for the derivation-induced dual-number morphism and the
formal-object differential.
-/

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

#check (FormalObject.toDualNumber :
  {R : CompleteLocalAlgCat Λ k} → Derivation Λ R.carrier k → R.carrier →ₐ[Λ] DualNumber k)
#check (FormalObject.toDualNumberHom :
  (ξ : FormalObject p) → Derivation Λ ξ.base.carrier k →
    (ξ.base.truncation 1 ⟶ ArtinianLocalAlgCat.dualNumber Λ k))
#check (FormalObject.differential :
  (ξ : FormalObject p) → [Functor.IsPredeformationCategory p] →
    Derivation Λ ξ.base.carrier k → Functor.tangentSpace p)
