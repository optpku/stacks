module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DirectedAffine.Points
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 70.5.1: Let `S` be a scheme. Let `X = lim_i X_i` be the limit of a
directed inverse system of algebraic spaces over `S` with affine transition
morphisms (Lemma 70.4.1). If each `X_i` is decent (for example quasi-separated,
by `instIsDecent_of_isQuasiSeparated`, or locally separated, by
`instIsDecent_of_isAbsolutelyLocallySeparated`) then `|X| = lim_i |X_i|` as
sets, as bijectivity of `Types.sectionOfCone (pointsFunctor.mapCone c)`. -/
@[stacks 0CUJ] #check
  (AlgebraicGeometry.AlgebraicSpace.DirectedAffine.bijective_sectionOfCone :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
      [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
      [∀ i : OrderDual I, IsDecent (D.obj i)]
      (c : Cone D) (hc : IsLimit c),
      Function.Bijective (Types.sectionOfCone (pointsFunctor.mapCone c)))
