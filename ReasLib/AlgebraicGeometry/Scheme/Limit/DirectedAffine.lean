/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import ReasLib.Topology.Category.TopCat.Limits.Recognition

/-!
# Explicit affine directed limits

This leaf provides the explicit affine candidate and comparison cone for a
directed inverse diagram of affine schemes.  It complements Mathlib's generic
limit-cone API with a named `Spec (colimit Γ)` construction.
-/

@[expose] public section

open CategoryTheory Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Limit.DirectedAffine

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u})

/-- A directed inverse diagram with affine transition morphisms admits a limit
cone in `Scheme`. -/
@[stacks 01YX]
theorem nonemptyCone
    (D : OrderDual I ⥤ Scheme.{u})
    [∀ {i j : OrderDual I} (f : i ⟶ j), IsAffineHom (D.map f)] :
    Nonempty (LimitCone D) := sorry

/-- A limit of a directed inverse diagram of nonempty quasi-compact schemes
with affine transition morphisms is nonempty. -/
theorem nonempty_of_isLimit
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : OrderDual I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : OrderDual I, Nonempty (D.obj i)]
    [∀ i : OrderDual I, CompactSpace (D.obj i)] :
    Nonempty c.pt := sorry

variable [∀ i, IsAffine (D.obj i)]

/-- The explicit affine candidate `Spec (colimit (D.op ⋙ Scheme.Γ))` for a
directed inverse diagram of affine schemes. -/
noncomputable abbrev scheme : Scheme.{u} :=
  Spec (colimit (D.op ⋙ Scheme.Γ))

/-- The canonical cone from `scheme D` to the stages of `D`. -/
noncomputable abbrev cone : Cone D :=
  let α : D ⟶ (D ⋙ Scheme.Γ.rightOp) ⋙ Scheme.Spec :=
    D.whiskerLeft ΓSpec.adjunction.unit
  have (i : OrderDual I) : IsIso (α.app i) := IsAffine.affine
  have : IsIso α := NatIso.isIso_of_isIso_app α
  (Cone.postcompose (asIso α).inv).obj <|
    Scheme.Spec.mapCone (coneOfCoconeLeftOp (colimit.cocone (D.op ⋙ Scheme.Γ)))

/-- The projection of the explicit affine limit cone at a stage. -/
@[simp]
theorem cone_π_app (i : OrderDual I) :
    (cone D).π.app i =
      Spec.map (colimit.ι (D.op ⋙ Scheme.Γ) (Opposite.op i)) ≫ (D.obj i).isoSpec.inv := sorry

/-- The explicit affine cone is a limit cone in `Scheme`. -/
@[stacks 01YW]
noncomputable def cone_isLimit : IsLimit (cone D) :=
  let α : D ⟶ (D ⋙ Scheme.Γ.rightOp) ⋙ Scheme.Spec :=
    D.whiskerLeft ΓSpec.adjunction.unit
  have (i : OrderDual I) : IsIso (α.app i) := IsAffine.affine
  have : IsIso α := NatIso.isIso_of_isIso_app α
  (IsLimit.postcomposeInvEquiv (asIso α) _).symm <|
    isLimitOfPreserves Scheme.Spec <|
      isLimitConeOfCoconeLeftOp (D ⋙ Scheme.Γ.rightOp) (colimit.isColimit _)

end

end AlgebraicGeometry.Scheme.Limit.DirectedAffine

namespace AlgebraicGeometry

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u})
variable [∀ {i j : OrderDual I} (f : i ⟶ j), IsAffineHom (D.map f)]

/-- The projections of a point of a cone over a directed inverse system of schemes are
compatible with every transition morphism. -/
theorem limitPointProjectionCompatible_of_directedAffineTransition
    (c : Cone D) {i j : OrderDual I} (f : i ⟶ j) (x : c.pt) :
    (D.map f) ((c.π.app i) x) = (c.π.app j) x := sorry

end


namespace Scheme.Limit.DirectedAffine

section


variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u})
variable [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]

/-- For a limiting cone of a directed inverse system of schemes with affine transition
morphisms, the canonical map from its points to compatible families of stagewise points is
bijective. -/
@[stacks 0CUE]
theorem bijective_sectionOfCone (c : Cone D) (hc : IsLimit c) :
    Function.Bijective (Types.sectionOfCone (Scheme.forget.mapCone c)) := sorry

/-- The underlying-topological-space functor preserves limits of directed
inverse diagrams of schemes whose transition morphisms are affine. -/
instance preservesLimit_forgetToTop : PreservesLimit D Scheme.forgetToTop := sorry

end


end Scheme.Limit.DirectedAffine

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D)
variable [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]

/-- A limiting cone of a directed inverse diagram of schemes with affine
transition morphisms remains limiting on underlying topological spaces. -/
@[stacks 0CUF]
noncomputable def isLimit_forgetToTop_mapCone_of_directedAffineTransition
    (hc : IsLimit c) : IsLimit (Scheme.forgetToTop.mapCone c) :=
  isLimitOfPreserves Scheme.forgetToTop hc

end

end AlgebraicGeometry
