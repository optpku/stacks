/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Scheme.Etale

/-- A presheaf on schemes satisfies the sheaf condition for a family of morphisms
if and only if its restriction fork is an equalizer. The parallel maps have
target the product over all ordered pairs of indices, including diagonal pairs. -/
theorem sheafCondition {U : Scheme.{u}} {ι : Type v} [Small.{u} ι]
    {X : ι → Scheme.{u}} (φ : ∀ i, X i ⟶ U)
    [(Presieve.ofArrows X φ).HasPairwisePullbacks] (F : Scheme.{u}ᵒᵖ ⥤ Type u) :
    (Presieve.ofArrows X φ).IsSheafFor F ↔
      Nonempty (IsLimit (Fork.ofι (Equalizer.Presieve.Arrows.forkMap F X φ)
        (Equalizer.Presieve.Arrows.w F X φ))) :=
  Equalizer.Presieve.Arrows.sheaf_condition F X φ

/-- A singleton family is an étale cover exactly when its morphism is
surjective on underlying spaces and étale. -/
theorem singletonCover_iff {X S : Scheme.{u}} (f : X ⟶ S) :
    Presieve.singleton f ∈ Scheme.precoverage @Etale S ↔
      Function.Surjective f.base ∧ Etale f :=
  Scheme.singleton_mem_precoverage_iff @Etale f

end AlgebraicGeometry.Scheme.Etale
