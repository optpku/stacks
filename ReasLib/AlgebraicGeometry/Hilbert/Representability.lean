/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Hilbert.Functor
public import ReasLib.AlgebraicGeometry.Hilbert.Sheaf
public import ReasLib.AlgebraicGeometry.Hilbert.Limit
public import ReasLib.AlgebraicGeometry.Hilbert.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.AffineOpen.FiniteSet
public import ReasLib.AlgebraicGeometry.Scheme.BigZariski.Representability
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Over
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiAffine.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Hilbert

/-- A finite family of points in one fiber of `X ⟶ S` is contained in an affine open of `X`. -/
class FiberPointsContainedInAffineOpen {S : Scheme.{u}} (X : Over S) (d : ℕ) : Prop where
  exists_affineOpen (s : S) (x : Fin d → X.left)
    (hx : ∀ i, X.hom.base (x i) = s) :
      ∃ U : X.left.affineOpens, ∀ i, x i ∈ (U : X.left.Opens)

/-- An affine scheme contains every finite family of its points in an affine open. -/
instance fiberPointsContainedInAffineOpen_of_isAffine {S : Scheme.{u}} (X : Over S) (d : ℕ)
    [IsAffine X.left] : FiberPointsContainedInAffineOpen X d := sorry

/-- For affine schemes `X ⟶ S` and a natural number `d`, the degree-`d` Hilbert
functor of `X` over `S` is representable. -/
@[instance]
theorem functor_isRepresentable_of_isAffine {S : Scheme.{u}} (X : Over S) (d : ℕ)
    [IsAffine X.left] [IsAffine S] :
    (functor X d).IsRepresentable := sorry

/-- If every finite family of points in a fiber of `X ⟶ S` lies in an affine open of `X`,
then the degree-`d` Hilbert functor of `X` over `S` is representable. -/
@[instance]
theorem functor_isRepresentable_of_fiber_points_contained_in_affineOpen
    {S : Scheme.{u}} (X : Over S) (d : ℕ)
    [FiberPointsContainedInAffineOpen X d] :
    (functor X d).IsRepresentable := sorry

/-- A quasi-affine scheme contains every finite family of points in an affine open. -/
@[instance]
theorem fiberPointsContainedInAffineOpen_of_isQuasiAffine
    {S : Scheme.{u}} (X : Over S) (d : ℕ) [X.left.IsQuasiAffine] :
    FiberPointsContainedInAffineOpen X d := sorry

/-- A quasi-affine morphism has an affine open containing every finite family of points
in one fiber. -/
theorem fiberPointsContainedInAffineOpen_of_quasiAffineHom
    {S : Scheme.{u}} (X : Over S) (d : ℕ) (hf : QuasiAffineHom X.hom) :
    FiberPointsContainedInAffineOpen X d := sorry

/-- A quasi-projective morphism has an affine open containing every finite family of points
in one fiber. -/
@[instance]
theorem fiberPointsContainedInAffineOpen_of_quasiProjective
    {S : Scheme.{u}} (X : Over S) (d : ℕ) [QuasiProjective X.hom] :
    FiberPointsContainedInAffineOpen X d := sorry

/-- A locally projective morphism has an affine open containing every finite family of points
in one fiber. -/
@[instance]
theorem fiberPointsContainedInAffineOpen_of_locallyProjective
    {S : Scheme.{u}} (X : Over S) (d : ℕ) [LocallyProjective X.hom] :
    FiberPointsContainedInAffineOpen X d := sorry

/-- A scheme with an ample invertible module contains every finite family of points
in an affine open. -/
theorem fiberPointsContainedInAffineOpen_of_hasAmpleInvertibleModule
    {S : Scheme.{u}} (X : Over S) (d : ℕ)
    (hX : Scheme.Modules.HasAmpleInvertibleModule X.left) :
    FiberPointsContainedInAffineOpen X d := sorry

/-- If a morphism admits a relatively ample module, every finite family of points
in one fiber is contained in an affine open of its source. -/
theorem fiberPointsContainedInAffineOpen_of_exists_relativelyAmple
    {S : Scheme.{u}} (X : Over S) (d : ℕ)
    (hL : ∃ L : X.left.Modules, RelativelyAmple X.hom L) :
    FiberPointsContainedInAffineOpen X d := sorry

/-- If a morphism admits a relatively very ample module, every finite family of points
in one fiber is contained in an affine open of its source. -/
theorem fiberPointsContainedInAffineOpen_of_exists_relativelyVeryAmple
    {S : Scheme.{u}} (X : Over S) (d : ℕ)
    (hL : ∃ L : X.left.Modules, RelativelyVeryAmple X.hom L) :
    FiberPointsContainedInAffineOpen X d := sorry

end AlgebraicGeometry.Hilbert
