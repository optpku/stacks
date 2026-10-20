/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompletionAlong

/-!
# Completion along a family of filtrations inducing the maximal-adic topology

Given a category cofibered in groupoids over `C_Λ` and a family of ideal
filtrations inducing the maximal-adic topology, one obtains a cofibered
category `hat F_I` over `hat C_Λ` whose fibres recover the `Along` fibres
and which is equivalent to ordinary completion by Lemma 90.7.4.
-/

@[expose] public section

open CategoryTheory FormalObject CompleteLocalAlgCat

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]

/- Remark 90.7.5 (1): the total filtration category projects cofiberedly to
the completed base category. -/
@[stacks 06H7] #check (CategoryTheory.Functor.completionAlong_op_isFiberedInGroupoids :
  ∀ (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op],
    Functor.IsFibered.InGroupoids (CategoryTheory.Functor.completionAlong I p).op)

/- Remark 90.7.5 (2): each fibre is strictly isomorphic to the corresponding
filtration-indexed fibre. -/
@[stacks 06H7] #check (FormalObject.AlongOver.ofAlong_isIso :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op]
    (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (R : CompleteLocalAlgCat Λ k),
    -- Local instance justification (defeq pin): the checked IsIso proposition must use the explicit Along.category stored in ofAlong, not an independently inferred category.
    letI := FormalObject.Along.category (p := p) (R := R) (I := I R)
    (FormalObject.AlongOver.ofAlong p I R).IsIso)

/- Remark 90.7.5 (3): the total filtration category is equivalent to ordinary
completion over the completed base. -/
@[stacks 06H7] #check (FormalObject.AlongOver.toCompletion_isEquivalence :
  ∀ (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op],
    BasedFunctor.IsEquivalence (FormalObject.AlongOver.toCompletionBased I p))

end
