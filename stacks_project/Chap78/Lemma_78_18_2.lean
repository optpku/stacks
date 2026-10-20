module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.InvariantOpen

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 78.18.2: for a groupoid in algebraic spaces over `B`, open source and
target maps make `s(t⁻¹(W))` invariant for every open `W`. If both maps are also
quasi-compact, the object space has a small Zariski covering by invariant
quasi-compact open subspaces. -/
@[stacks 044G] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.isOpenInvariant_sImageTPreimage :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
      [AlgebraicSpace.Open G.s.left] [AlgebraicSpace.Open G.t.left]
      (W : OpenSubspace G.U.left),
      CategoryTheory.Morphism.IsForwardInvariant G.s.left G.t.left
        (AlgebraicGeometry.GroupoidAlgebraicSpace.sImageTPreimage G W).ι)

#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.exists_invariantQuasiCompactOpenCover :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
      [AlgebraicSpace.Open G.s.left] [AlgebraicSpace.Open G.t.left]
      [AlgebraicSpace.QuasiCompact G.s.left] [AlgebraicSpace.QuasiCompact G.t.left],
      ∃ (ι : Type u) (_ : Small.{u} ι) (𝒰 : ι → OpenSubspace G.U.left),
        IsZariskiCover G.U.left (fun i ↦ (𝒰 i).X) (fun i ↦ (𝒰 i).ι) ∧
          ∀ i, CategoryTheory.Morphism.IsForwardInvariant G.s.left G.t.left (𝒰 i).ι ∧
            IsQuasiCompact (𝒰 i).X)
