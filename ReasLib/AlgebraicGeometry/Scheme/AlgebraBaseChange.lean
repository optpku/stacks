/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AlgebraBaseChange

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (A : CommRingCat.{u}) (B : I ⥤ CommRingCat.{u})
variable (σ : (Functor.const I).obj A ⟶ B)

/-- The structure map from the base ring to the colimit of a directed algebra diagram. -/
def fromBase [HasColimit B] : A ⟶ colimit B :=
  σ.app (Classical.arbitrary I) ≫ colimit.ι B (Classical.arbitrary I)

omit [IsDirected I (· ≤ ·)] in
/-- Every stage structure map induces the same map into the directed colimit. -/
theorem fromBase_ι [IsDirected I (· ≤ ·)] [HasColimit B] (i : I) :
    σ.app i ≫ colimit.ι B i = fromBase A B σ := sorry

/-- The structure morphism from the spectrum of a stage algebra to the base spectrum. -/
def specMap (i : I) :
    Scheme.Spec.obj (op (B.obj i)) ⟶ Scheme.Spec.obj (op A) :=
  Scheme.Spec.map (σ.app i).op

/-- The structure morphism from the spectrum of the colimit algebra to the base spectrum. -/
def specColimitMap [HasColimit B] :
    Scheme.Spec.obj (op (colimit B)) ⟶ Scheme.Spec.obj (op A) :=
  Scheme.Spec.map (fromBase A B σ).op

/-- The base change of `X` along the spectrum of a stage algebra. -/
abbrev stage {X : Scheme.{u}} (f : X ⟶ Scheme.Spec.obj (op A)) (i : I) : Scheme.{u} :=
  pullback f (specMap A B σ i)

/-- The projection from a stage base change to `X`. -/
def projection {X : Scheme.{u}} (f : X ⟶ Scheme.Spec.obj (op A)) (i : I) :
    stage A B σ f i ⟶ X :=
  pullback.fst f (specMap A B σ i)

/-- The projection from a stage base change to the stage affine scheme. -/
def affineProjection {X : Scheme.{u}} (f : X ⟶ Scheme.Spec.obj (op A)) (i : I) :
    stage A B σ f i ⟶ Scheme.Spec.obj (op (B.obj i)) :=
  pullback.snd f (specMap A B σ i)

/-- The stage pullback square is compatible with the transition of algebras. -/
theorem transition_comm {X : Scheme.{u}} (f : X ⟶ Scheme.Spec.obj (op A))
    {i j : I} (hij : i ≤ j) :
    projection A B σ f j ≫ f =
      (affineProjection A B σ f j ≫ Scheme.Spec.map (B.map (homOfLE hij)).op) ≫
        specMap A B σ i := sorry

/-- The transition from the later stage base change to the earlier stage base change. -/
def transition {X : Scheme.{u}} (f : X ⟶ Scheme.Spec.obj (op A)) {i j : I} (hij : i ≤ j) :
    stage A B σ f j ⟶ stage A B σ f i :=
  pullback.lift (projection A B σ f j)
    (affineProjection A B σ f j ≫ Scheme.Spec.map (B.map (homOfLE hij)).op)
    (transition_comm A B σ f hij)

/-- The base change of `X` along the spectrum of the colimit algebra. -/
abbrev limit [HasColimit B] {X : Scheme.{u}} (f : X ⟶ Scheme.Spec.obj (op A)) : Scheme.{u} :=
  pullback f (specColimitMap A B σ)

/-- The projection from the colimit base change to `X`. -/
def limitProjection [HasColimit B] {X : Scheme.{u}} (f : X ⟶ Scheme.Spec.obj (op A)) :
    limit A B σ f ⟶ X :=
  pullback.fst f (specColimitMap A B σ)

/-- The projection from the colimit base change to the spectrum of the colimit algebra. -/
def limitAffineProjection [HasColimit B] {X : Scheme.{u}} (f : X ⟶ Scheme.Spec.obj (op A)) :
    limit A B σ f ⟶ Scheme.Spec.obj (op (colimit B)) :=
  pullback.snd f (specColimitMap A B σ)

omit [IsDirected I (· ≤ ·)] in
/-- The colimit base-change square is compatible with every stage inclusion. -/
theorem fromLimit_comm [IsDirected I (· ≤ ·)] [HasColimit B] {X : Scheme.{u}}
    (f : X ⟶ Scheme.Spec.obj (op A)) (i : I) :
    limitProjection A B σ f ≫ f =
      (limitAffineProjection A B σ f ≫ Scheme.Spec.map (colimit.ι B i).op) ≫
        specMap A B σ i := sorry

/-- The canonical morphism from the colimit base change to a stage base change. -/
def fromLimit [HasColimit B] {X : Scheme.{u}} (f : X ⟶ Scheme.Spec.obj (op A)) (i : I) :
    limit A B σ f ⟶ stage A B σ f i :=
  pullback.lift (limitProjection A B σ f)
    (limitAffineProjection A B σ f ≫ Scheme.Spec.map (colimit.ι B i).op)
    (fromLimit_comm A B σ f i)

/-- A stage transition preserves the projection to the base scheme. -/
theorem transition_projection {X : Scheme.{u}} (f : X ⟶ Scheme.Spec.obj (op A))
    {i j : I} (hij : i ≤ j) :
    transition A B σ f hij ≫ projection A B σ f i = projection A B σ f j := sorry

/-- A colimit-to-stage map preserves the projection to the base scheme. -/
theorem fromLimit_projection [HasColimit B] {X : Scheme.{u}}
    (f : X ⟶ Scheme.Spec.obj (op A)) (i : I) :
    fromLimit A B σ f i ≫ projection A B σ f i = limitProjection A B σ f := sorry

end AlgebraicGeometry.Scheme.AlgebraBaseChange

end
