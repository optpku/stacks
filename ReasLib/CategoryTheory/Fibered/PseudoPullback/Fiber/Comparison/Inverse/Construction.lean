/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Projections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Construction of the inverse fibre comparison

This leaf constructs the functor from the categorical pullback of the two fibres over `U` to the
actual fibre of the based pseudo-pullback. Object and morphism readouts are provided by the
separate `Inverse.Computations` leaf.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open Functor.IsHomLift
open Functor.Fiber
open CategoricalPullback
open scoped CategoricalPullback

universe u v uX uY uS vX vY vS

namespace CategoryTheory
namespace BasedCategory

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}
variable (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)

noncomputable section

namespace PseudoPullback
namespace Fiber

section ComparisonInverseImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The component maps of a morphism in the pullback of fibres form the comparison square
required in the total pseudo-pullback. -/
private theorem fromPullbackTotalMapComm
    {U : C} {P Q : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)}
    (φ : P ⟶ Q) :
    CommSq (F.toFunctor.map φ.fst.1) P.iso.hom.1 Q.iso.hom.1
      (G.toFunctor.map φ.snd.1) := sorry

/-- The total pseudo-pullback object represented by a pullback object in the fibres over U. -/
private def fromPullbackTotalObj
    (U : C) (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    (PseudoPullback F G).obj :=
  PseudoPullback.mk F G U P

/-- The total pseudo-pullback morphism represented by a morphism in the pullback of fibres. -/
private def fromPullbackTotalMap
    {U : C} {P Q : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)}
    (φ : P ⟶ Q) :
    fromPullbackTotalObj F G U P ⟶ fromPullbackTotalObj F G U Q :=
  PseudoPullback.Hom.mk (𝟙 U) φ.fst.1 φ.fst.2 φ.snd.1 φ.snd.2
    (fromPullbackTotalMapComm F G φ)

/-- The total pseudo-pullback map preserves identity morphisms. -/
private theorem fromPullbackTotalMapId
    (U : C) (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    fromPullbackTotalMap F G (𝟙 P) =
      𝟙 (fromPullbackTotalObj F G U P) := sorry

/-- The total pseudo-pullback map preserves composition. -/
private theorem fromPullbackTotalMapComp
    {U : C} {P Q R : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)}
    (φ : P ⟶ Q) (ψ : Q ⟶ R) :
    fromPullbackTotalMap F G (φ ≫ ψ) =
      fromPullbackTotalMap F G φ ≫ fromPullbackTotalMap F G ψ := sorry

/-- The pullback of the fibres over U, viewed in the total category of the bundled
pseudo-pullback over C. -/
private def fromPullbackTotal
    (U : C) :
    (F.fiberFunctor U) ⊡ (G.fiberFunctor U) ⥤ (PseudoPullback F G).obj where
  obj := fromPullbackTotalObj F G U
  map := fromPullbackTotalMap F G
  map_id := fromPullbackTotalMapId F G U
  map_comp := fromPullbackTotalMapComp F G

/-- The total comparison functor lies strictly over the constant functor at U. -/
private theorem fromPullbackTotalCompProjection
    (U : C) :
    fromPullbackTotal F G U ⋙ (PseudoPullback F G).p =
      (Functor.const ((F.fiberFunctor U) ⊡ (G.fiberFunctor U))).obj U := sorry

end Implementation

/-- The explicit inverse to the fibre comparison, from the pullback model over `U` to the
actual fibre of the bundled pseudo-pullback. -/
@[stacks 02XI "inverse fibre comparison for a based pseudo-pullback"]
def comparisonInverse
    (U : C) :
    (F.fiberFunctor U) ⊡ (G.fiberFunctor U) ⥤
      Functor.Fiber (PseudoPullback F G).p U :=
  Functor.Fiber.inducedFunctor (Implementation.fromPullbackTotalCompProjection F G U)

end ComparisonInverseImplementation

end Fiber
end PseudoPullback
end

end BasedCategory
end CategoryTheory
