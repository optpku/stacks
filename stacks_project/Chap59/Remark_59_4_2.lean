/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SheafCondition
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

variable {U : Scheme.{u}} {ι : Type v} [Small.{u} ι] {X : ι → Scheme.{u}}
variable (φ : ∀ i, X i ⟶ U)
variable [(Presieve.ofArrows X φ).HasPairwisePullbacks]
variable (F : Scheme.{u}ᵒᵖ ⥤ Type u)

/- Remark 59.4.2 (1): the étale sheaf equalizer for an ofArrows covering uses
the product over all pairs `i, j`, including `i = j` as `F(U_i ×_U U_i)`.
Unlike Zariski open immersions, that diagonal self-fiber product is in general
nontrivial. -/
@[stacks 03N6] #check (AlgebraicGeometry.Scheme.Etale.sheafCondition φ F :
  (Presieve.ofArrows X φ).IsSheafFor F ↔
    Nonempty (IsLimit (Fork.ofι (Equalizer.Presieve.Arrows.forkMap F X φ)
      (Equalizer.Presieve.Arrows.w F X φ))))


/- Remark 59.4.2 (2): important étale coverings are often singleton families;
a map is an étale covering of `S` iff it is étale and surjective on underlying
spaces, so the sheaf axiom reduces to the equalizer `F(S) → F(T) ⇉ F(T ×_S T)`. -/
@[stacks 03N6] #check (AlgebraicGeometry.Scheme.Etale.singletonCover_iff :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S),
    Presieve.singleton f ∈ Scheme.precoverage @Etale S ↔
      Function.Surjective f.base ∧ Etale f)
