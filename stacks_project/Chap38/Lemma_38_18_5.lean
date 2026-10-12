/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Limit.Purity
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

/- Lemma 38.18.5: a finitely presented scheme and finitely presented quasicoherent module over
a directed inverse limit of affine schemes descend to one stage while remaining pure and flat
along the fibre over the projected point. -/
@[stacks 05MA] #check
  (AlgebraicGeometry.Scheme.Modules.IsPureAlong.exists_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ AlgebraicGeometry.Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [∀ i, AlgebraicGeometry.IsAffine (D.obj i)]
      (X : Over c.pt) [AlgebraicGeometry.Scheme.Hom.FinitePresentation X.hom]
      (ℱ : X.left.Modules) [ℱ.IsFinitePresentation] (s : c.pt)
      (h_pure : ℱ.IsPureAlong X.hom s)
      (h_flat : ∀ x : X.hom.fiber s,
        AlgebraicGeometry.Scheme.Modules.flatOverAt ℱ X.hom (X.hom.fiberι s x)),
      ∃ (i : I)
        (Xi : AlgebraicGeometry.FinitePresentationOver (D.obj i))
        (ℱi : AlgebraicGeometry.FinitePresentationModules Xi.obj.left)
        (g : X.left ⟶ Xi.obj.left),
        IsPullback g X.hom Xi.obj.hom (c.π.app i) ∧
          ℱi.obj.IsPureAlong Xi.obj.hom ((c.π.app i) s) ∧
          (∀ x : AlgebraicGeometry.Scheme.Hom.fiber Xi.obj.hom ((c.π.app i) s),
            AlgebraicGeometry.Scheme.Modules.flatOverAt ℱi.obj Xi.obj.hom
              (AlgebraicGeometry.Scheme.Hom.fiberι Xi.obj.hom ((c.π.app i) s) x)) ∧
          Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback g).obj ℱi.obj ≅ ℱ))
