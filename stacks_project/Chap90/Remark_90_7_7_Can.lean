/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Completion.Restriction

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]

/- Remark 90.7.7: compatibility checks for restriction and canonical evaluation. -/
#check (FormalObject.Restrict : (F ⥤ ArtinianLocalAlgCat Λ k) → Type (max (u + 1) v))

#check (FormalObject.can : ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k)
  [Functor.IsFibered.InGroupoids p.op], FormalObject.Restrict p ⥤ F)

#check (FormalObject.basedCan_isEquivalence : ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k)
  [Functor.IsFibered.InGroupoids p.op], BasedFunctor.IsEquivalence (FormalObject.basedCan p))

#check (FormalObject.embed : ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k)
  [Functor.IsFibered.InGroupoids p.op], F ⥤ FormalObject p)
