/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Completion.Restriction

import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]

/- Remark 90.7.7: evaluation at the least vanishing maximal-adic truncation is a canonical
 equivalence of categories cofibered in groupoids over the Artinian base. -/
@[stacks 06SJ] #check (FormalObject.basedCan_isEquivalence :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op],
    BasedFunctor.IsEquivalence (FormalObject.basedCan p))

#check (FormalObject.can : ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k)
  [Functor.IsFibered.InGroupoids p.op], FormalObject.Restrict p ⥤ F)

#check (FormalObject.can_obj : ∀ {p : F ⥤ ArtinianLocalAlgCat Λ k}
  [Functor.IsFibered.InGroupoids p.op] (ξ : FormalObject.Restrict p),
  (FormalObject.can p).obj ξ = FormalObject.canObj ξ)

#check (FormalObject.embed : ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k)
  [Functor.IsFibered.InGroupoids p.op], F ⥤ FormalObject p)

#check (FormalObject.toRestrict_isQuasiInverse : ∀ {p : F ⥤ ArtinianLocalAlgCat Λ k}
  [Functor.IsFibered.InGroupoids p.op],
  Nonempty (𝟭 (FormalObject.Restrict p) ≅ FormalObject.can p ⋙ FormalObject.toRestrict p) ∧
    Nonempty (FormalObject.toRestrict p ⋙ FormalObject.can p ≅ 𝟭 F))
