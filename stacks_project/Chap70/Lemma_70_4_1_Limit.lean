/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap70.«70_4_1_1_Comparison»

/-!
# Directed affine inverse limits of algebraic spaces

The inverse limit of a directed system of algebraic spaces with affine
transition morphisms, constructed as the `Type u` limit of functors of
points and packaged by `ofFunctor`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits (HasLimit Cone IsLimit)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DirectedAffine

variable {I : Type u} [Preorder I] [h_nonempty : Nonempty I]
variable [h_directed : IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
variable [h_affine : ∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]

include h_nonempty h_directed h_affine

/-- The functor of points of a directed affine inverse system is an fppf sheaf. -/
theorem limit_isSheaf :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S)
      (Limits.limit (D ⋙ forgetToPresheaf)) :=
  sorry

/-- The diagonal of the inverse limit of functors of points is relatively
representable by schemes. -/
theorem limit_representableDiagonal :
    yoneda.relativelyRepresentable
      (Limits.diag (Limits.limit (D ⋙ forgetToPresheaf))) :=
  sorry

/-- The inverse limit of functors of points admits a representable étale
locally surjective atlas. -/
theorem limit_exists_atlas :
    ∃ (U : Over S) (p : yoneda.obj U ⟶ Limits.limit (D ⋙ forgetToPresheaf)),
      MorphismProperty.presheaf (MorphismProperty.over (@Etale)) p ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p :=
  sorry

/-- The inverse limit of a directed affine system of algebraic spaces over `S`,
as the algebraic space whose functor of points is the inverse limit of the
functors of points. -/
def limit : AlgebraicSpace S :=
  ofFunctor (Limits.limit (D ⋙ forgetToPresheaf))
    (limit_isSheaf D) (limit_representableDiagonal D) (limit_exists_atlas D)

/-- The functor of points of `limit D` is the inverse limit of the functors of
points of the stages. -/
theorem limit_functorOfPoints :
    (limit D).functorOfPoints = Limits.limit (D ⋙ forgetToPresheaf) :=
  sorry

/-- Naturality of the projections of the presheaf-level inverse limit, viewed as
morphisms of algebraic spaces. -/
theorem limitCone_π_naturality ⦃i j : OrderDual I⦄ (f : i ⟶ j) :
    ((Functor.const (OrderDual I)).obj (limit D)).map f ≫
        Limits.limit.π (D ⋙ forgetToPresheaf) j =
      Limits.limit.π (D ⋙ forgetToPresheaf) i ≫ D.map f :=
  sorry

/-- The inverse limit cone of a directed affine system of algebraic spaces. -/
def limitCone : Cone D where
  pt := limit D
  π :=
    { app := fun i ↦ Limits.limit.π (D ⋙ forgetToPresheaf) i
      naturality := limitCone_π_naturality D }

/-- The mediating morphism of algebraic spaces induced by a cone over `D`. -/
def limitCone_lift (s : Cone D) : s.pt ⟶ (limitCone D).pt :=
  Limits.limit.lift (D ⋙ forgetToPresheaf) (forgetToPresheaf.mapCone s)

/-- The mediating morphism recovers the given cone projection at each stage. -/
theorem limitCone_lift_fac (s : Cone D) (j : OrderDual I) :
    limitCone_lift D s ≫ (limitCone D).π.app j = s.π.app j :=
  sorry

/-- The mediating morphism is the unique cone morphism to `limitCone D`. -/
theorem limitCone_lift_uniq (s : Cone D) (m : s.pt ⟶ (limitCone D).pt)
    (w : ∀ j, m ≫ (limitCone D).π.app j = s.π.app j) :
    m = limitCone_lift D s :=
  sorry

/-- The cone `limitCone D` is a limit cone in `AlgebraicSpace S`. -/
def limitCone_isLimit : IsLimit (limitCone D) where
  lift := limitCone_lift D
  fac := limitCone_lift_fac D
  uniq := limitCone_lift_uniq D

/-- A directed inverse system of algebraic spaces over `S` with affine
transitions has a limit. -/
instance hasLimit : HasLimit D :=
  HasLimit.mk ⟨limitCone D, limitCone_isLimit D⟩

/-- Each projection from the inverse limit of a directed affine system of
algebraic spaces is affine. -/
instance affine_π (i : OrderDual I) : Affine (Limits.limit.π D i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DirectedAffine
