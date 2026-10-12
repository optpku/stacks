/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Pseudofunctor.Construction.Basic

/-!
# Action of the explicit pseudo-pullback pseudofunctor

Computation rules for its object, morphism, `2`-cell, and comparison actions.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open BasedNatIso
open Functor.IsHomLift
open Functor.Fiber
open CategoricalPullback
open scoped CategoricalPullback
open scoped Bicategory BasedFunctor Pseudofunctor.StrongTrans

universe u v w vB

namespace CategoryTheory

open Bicategory

namespace BasedCategory

variable {C : Type u} [Category.{v} C]

namespace PseudoPullback

noncomputable section

/-- The object action of the explicit pseudo-pullback pseudofunctor is the computational
pseudo-pullback of the two bundled cospan legs. -/
@[simp]
theorem pseudofunctor.obj
    (S : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)) :
    (pseudofunctor C).obj S = PseudoPullback S.fst S.snd := sorry

/-- The `1`-cell action of the explicit pseudo-pullback pseudofunctor is the existing
componentwise pseudo-pullback map. -/
@[simp]
theorem pseudofunctor.map
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : S ⟶ T) :
    (pseudofunctor C).map ψ =
      map (Bicategory.Cospan.Hom.toBasedTransform ψ) := sorry

/-- The `2`-cell action of the explicit pseudo-pullback pseudofunctor is the existing
componentwise based natural transformation. -/
@[simp]
theorem pseudofunctor.map₂
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ) :
    (pseudofunctor C).map₂ Γ =
      _root_.CategoryTheory.BasedCategory.PseudoPullback.map₂
        (Bicategory.Cospan.Hom₂.toBasedModification Γ) := sorry

/-- The identity comparison of the explicit pseudo-pullback pseudofunctor transports across the
bundled-cospan identity bridge and then uses the componentwise identity isomorphism. -/
@[simp]
theorem pseudofunctor.mapId
    (S : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)) :
    (pseudofunctor C).mapId S =
      eqToIso (congrArg
        (fun theta : BasedCospanTransform S.fst S.snd S.fst S.snd =>
          _root_.CategoryTheory.BasedCategory.PseudoPullback.map theta)
        (Bicategory.Cospan.Hom.toBasedTransform.id S)) ≪≫
        _root_.CategoryTheory.BasedCategory.PseudoPullback.map.idIso S.fst S.snd := sorry

/-- The composition comparison of the explicit pseudo-pullback pseudofunctor transports across
the bundled-cospan composition bridge and then uses the componentwise composition isomorphism. -/
@[simp]
theorem pseudofunctor.mapComp
    {R S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : R ⟶ S) (φ : S ⟶ T) :
    (pseudofunctor C).mapComp ψ φ =
      eqToIso (congrArg
        (fun theta : BasedCospanTransform R.fst R.snd T.fst T.snd =>
          _root_.CategoryTheory.BasedCategory.PseudoPullback.map theta)
        (Bicategory.Cospan.Hom.toBasedTransform.comp ψ φ)) ≪≫
        _root_.CategoryTheory.BasedCategory.PseudoPullback.map.compIso
          (Bicategory.Cospan.Hom.toBasedTransform ψ)
          (Bicategory.Cospan.Hom.toBasedTransform φ) := sorry

/-- On each hom category, the explicit pseudo-pullback pseudofunctor is the computational
hom functor after forgetting the induced cospan wrapper. -/
@[simp]
theorem pseudofunctor.mapFunctor
    (S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)) :
    (pseudofunctor C).mapFunctor S T =
      Bicategory.Cospan.basedTransformFunctor S T ⋙
        _root_.CategoryTheory.BasedCategory.PseudoPullback.mapFunctor
          (F₁ := S.fst) (G₁ := S.snd)
          (F₂ := T.fst) (G₂ := T.snd) := sorry

end

end PseudoPullback

end BasedCategory

end CategoryTheory
