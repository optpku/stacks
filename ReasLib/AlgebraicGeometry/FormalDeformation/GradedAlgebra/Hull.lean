module

public import ReasLib.AlgebraicGeometry.FormalDeformation.GradedAlgebra.Tangent
public import ReasLib.AlgebraicGeometry.FormalDeformation.GradedAlgebra.RimSchlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.IsoClass

/-!
# Hulls of isomorphism classes of graded-algebra deformations

In the classical case, if `P` is a finitely generated graded `k`-algebra, the
set-valued functor of isomorphism classes of objects of `Def_P` admits a hull.
-/

@[expose] public section

open CategoryTheory Functor

noncomputable section

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (Λ)

namespace FiniteProjectiveGradedAlgebraCat

/-- The canonical projection from deformations of a locally finite graded algebra,
with its morphism universe lifted to the object universe. -/
abbrev deformationForgetULift (P : FiniteProjectiveGradedAlgebra k) :
    ULiftHom.{u + 1} (deformationCategory Λ k P) ⥤ ArtinianLocalAlgCat Λ k :=
  ULiftHom.down ⋙ deformationForget Λ P

/-- `deformationForgetULift` is `ULiftHom.down` followed by `deformationForget`. -/
theorem deformationForgetULift_eq (P : FiniteProjectiveGradedAlgebra k) :
    deformationForgetULift Λ P = ULiftHom.down ⋙ deformationForget Λ P := sorry

/-- Evaluating `deformationForgetULift` on a Hom-universe lift recovers
`deformationForget`. -/
theorem deformationForgetULift_obj (P : FiniteProjectiveGradedAlgebra k)
    (ξ : deformationCategory Λ k P) :
    (deformationForgetULift Λ P).obj (ULiftHom.objUp ξ) =
      (deformationForget Λ P).obj ξ := sorry

/-- The Hom-universe lift of the canonical graded-algebra deformation projection
is a predeformation category. -/
instance instIsPredeformationCategory_deformationForgetULift
    (P : FiniteProjectiveGradedAlgebra k) :
    IsPredeformationCategory (deformationForgetULift Λ P) := sorry

/-- The opposite of the lifted graded-algebra deformation projection is fibered
in groupoids. -/
instance instIsFiberedInGroupoids_deformationForgetULift_op
    (P : FiniteProjectiveGradedAlgebra k) :
    IsFibered.InGroupoids (deformationForgetULift Λ P).op :=
  IsPredeformationCategory.isCofiberedInGroupoids

/-- Over a classical complete local base with residue field k, the functor of
isomorphism classes of deformations of a finitely generated, locally finite
commutative graded k-algebra has a hull. -/
@[stacks 0ET3]
theorem exists_isHull_isoClass (P : FiniteProjectiveGradedAlgebra k)
    [Algebra.FiniteType k P.carrier] [ArtinianLocalAlgCat.IsClassical Λ k] :
    ∃ ξ : FormalObject (isoClassProjection (deformationForgetULift Λ P)),
      FormalObject.IsHull ξ := sorry

end FiniteProjectiveGradedAlgebraCat
