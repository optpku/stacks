module

public import ReasLib.AlgebraicGeometry.Scheme.Reduced
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 28.3.2: for a scheme, reducedness is equivalent to reduced section rings on one
affine open cover, on every affine open, and on every open. -/
@[stacks 01OL] #check
  (AlgebraicGeometry.IsReduced.tfae :
    ∀ (X : Scheme.{u}),
      List.TFAE [
        AlgebraicGeometry.IsReduced X,
        ∃ 𝒰 : X.AffineOpenCover,
          ∀ i : 𝒰.I₀, _root_.IsReduced Γ(X, (𝒰.f i).opensRange),
        ∀ U : X.affineOpens, _root_.IsReduced Γ(X, U),
        ∀ U : X.Opens, _root_.IsReduced Γ(X, U)])

#check
  (AlgebraicGeometry.IsReduced.iff_exists_affineOpenCover :
    ∀ (X : Scheme.{u}),
      AlgebraicGeometry.IsReduced X ↔
        ∃ 𝒰 : X.AffineOpenCover,
          ∀ i : 𝒰.I₀, _root_.IsReduced Γ(X, (𝒰.f i).opensRange))

#check
  (AlgebraicGeometry.IsReduced.iff_forall_affineOpen :
    ∀ (X : Scheme.{u}),
      AlgebraicGeometry.IsReduced X ↔
        ∀ U : X.affineOpens, _root_.IsReduced Γ(X, U))

#check
  (AlgebraicGeometry.Scheme.isReduced_iff :
    ∀ (X : Scheme.{u}),
      AlgebraicGeometry.IsReduced X ↔
        ∀ U : X.Opens, _root_.IsReduced Γ(X, U))
