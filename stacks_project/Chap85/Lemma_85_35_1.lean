module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.FppfHomDescent
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Simplicial
open CategoryTheory.ComposableArrows Functor
open scoped DerivedExt Simplicial ZeroObject

noncomputable section

universe u

/- Lemma 85.35.1 (1). -/
@[stacks 0DL9] #check
  (AlgebraicGeometry.AlgebraicSpace.Simplicial.negExtSubsingleton :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      {U : SimplicialObject (AlgebraicSpace S)}
      (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (ha : IsFppfHypercovering a)
    (K E : AlgebraicSpace.DerivedQCoh X)
    (h_ext : ∀ n : ℕ, ∀ i : ℤ, i < 0 →
      Subsingleton
        (Ext⁽i⁾((modulePullbackDerived (a.app (op ⦋n⦌))).obj K.obj,
          (modulePullbackDerived (a.app (op ⦋n⦌))).obj E.obj)))
    (i : ℤ) (hi : i < 0),
    Subsingleton (Ext⁽i⁾(K.obj, E.obj)))

/- Lemma 85.35.1 (2). -/
@[stacks 0DL9] #check
  (AlgebraicGeometry.AlgebraicSpace.Simplicial.homSequence_exact :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      {U : SimplicialObject (AlgebraicSpace S)}
      (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (ha : IsFppfHypercovering a)
    (K E : AlgebraicSpace.DerivedQCoh X)
    (h_ext : ∀ n : ℕ, ∀ i : ℤ, i < 0 →
      Subsingleton
        (Ext⁽i⁾((modulePullbackDerived (a.app (op ⦋n⦌))).obj K.obj,
          (modulePullbackDerived (a.app (op ⦋n⦌))).obj E.obj))),
    (mk₃ (0 : 0 ⟶ AddCommGrpCat.of (K.obj ⟶ E.obj))
      (homRestrict a K E) (homDiff a K E)).Exact)

end
