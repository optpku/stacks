module

public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.AdicCompletion
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.IsoClass

/-!
# Hulls of isomorphism classes of ring deformations

Over a classical complete local base, the functor of isomorphism classes of
deformations of a finite type algebra with finite nonsmooth locus has a hull.
-/

@[expose] public section

open Algebra CategoryTheory Functor

noncomputable section

universe u

namespace FlatAlgebraCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The canonical projection from flat deformations of an algebra to their Artinian
local bases, with its morphism universe lifted to the object universe. -/
abbrev deformationForgetULift (P : Type u) [CommRing P] [Algebra k P] :
    ULiftHom.{u + 1} (deformationCategory Λ k P) ⥤ ArtinianLocalAlgCat Λ k :=
  ULiftHom.down ⋙ deformationForget Λ k P

/-- The lifted deformation projection is the universe-forgetful functor followed by
the canonical deformation projection. -/
theorem deformationForgetULift_eq (P : Type u) [CommRing P] [Algebra k P] :
    deformationForgetULift Λ k P = ULiftHom.down ⋙ deformationForget Λ k P :=
  rfl

/-- The lifted deformation projection sends a lifted deformation to its original
Artinian local base. -/
theorem deformationForgetULift_obj (P : Type u) [CommRing P] [Algebra k P]
    (ξ : deformationCategory Λ k P) :
    (deformationForgetULift Λ k P).obj (ULiftHom.objUp ξ) =
      (deformationForget Λ k P).obj ξ :=
  rfl

/-- The lifted projection from flat deformations of an algebra to Artinian local
bases is a predeformation category. -/
instance instIsPredeformationCategory_deformationForgetULift
    (P : Type u) [CommRing P] [Algebra k P] :
    IsPredeformationCategory (deformationForgetULift Λ k P) :=
  sorry

/-- The opposite of the lifted flat-algebra deformation projection is fibered
in groupoids. -/
instance instIsFiberedInGroupoids_deformationForgetULift_op
    (P : Type u) [CommRing P] [Algebra k P] :
    IsFibered.InGroupoids (deformationForgetULift Λ k P).op :=
  IsPredeformationCategory.isCofiberedInGroupoids

/-- Over a classical complete local base with residue field `k`, the functor of
isomorphism classes of flat deformations of a finite type commutative `k`-algebra
whose nonsmooth locus is finite has a hull. -/
@[stacks 0ET4]
theorem exists_isHull_isoClass (P : Type u) [CommRing P] [Algebra k P]
    [Algebra.FiniteType k P] [ArtinianLocalAlgCat.IsClassical Λ k]
    (h_nonsmooth : (smoothLocus k P)ᶜ.Finite) :
    ∃ ξ : FormalObject (isoClassProjection (deformationForgetULift Λ k P)),
      FormalObject.IsHull ξ :=
  sorry

end FlatAlgebraCat
