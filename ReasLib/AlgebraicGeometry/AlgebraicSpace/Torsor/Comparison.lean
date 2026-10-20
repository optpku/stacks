/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Hom.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Principal.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Torsor.Category
public import ReasLib.AlgebraicGeometry.GroupScheme.AlgebraicSpace
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic

/-!
# Viewing fppf torsors as principal homogeneous spaces

The comparison 1-morphism of stacks sending an fppf `G_U`-torsor to the same
object viewed as a principal homogeneous `G`-space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupAlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)

/-- Send an fppf `G_U`-torsor to the same action viewed as a principal homogeneous
`G_U`-space. -/
def toPrincipalObj (ξ : Torsors.Obj G) : Principal.Obj G where
  U := ξ.U
  b := ξ.b
  X := ξ.X
  isPrincipal := ξ.isTorsor.isTorsor

/-- The comparison on objects preserves the underlying scheme, morphism to `B`,
and action. -/
theorem toPrincipalObj_spec (ξ : Torsors.Obj G) :
    (toPrincipalObj G ξ).U = ξ.U ∧ (toPrincipalObj G ξ).b = ξ.b ∧
      (toPrincipalObj G ξ).X = ξ.X := sorry

/-- Send a morphism of fppf `G_U`-torsors to the same scheme map and equivariant
isomorphism of principal homogeneous spaces. -/
def toPrincipalMap {ξ ξ' : Torsors.Obj G} (α : Torsors.Hom ξ ξ') :
    Principal.Hom (toPrincipalObj G ξ) (toPrincipalObj G ξ') where
  f := α.f
  comm := α.comm
  g := α.g
  equivariant := sorry

/-- The comparison on morphisms preserves the underlying scheme map and
equivariant isomorphism. -/
theorem toPrincipalMap_spec {ξ ξ' : Torsors.Obj G} (α : Torsors.Hom ξ ξ') :
    (toPrincipalMap G α).f = α.f ∧ (toPrincipalMap G α).g = α.g := sorry

/-- The comparison functor sends identity morphisms to identity morphisms. -/
theorem toPrincipalFunctor_map_id (ξ : Torsors.Obj G) :
    toPrincipalMap G (Torsors.idHom ξ) = Principal.idHom (toPrincipalObj G ξ) :=
  sorry

/-- The comparison functor preserves composition. -/
theorem toPrincipalFunctor_map_comp {ξ ξ' ξ'' : Torsors.Obj G}
    (α : Torsors.Hom ξ ξ') (β : Torsors.Hom ξ' ξ'') :
    toPrincipalMap G (Torsors.compHom α β) =
      Principal.compHom (toPrincipalMap G α) (toPrincipalMap G β) := sorry

/-- The comparison functor on objects of `G`-Torsors and `G`-Principal. -/
def toPrincipalFunctor : Torsors.Obj G ⥤ Principal.Obj G where
  obj ξ := toPrincipalObj G ξ
  map α := toPrincipalMap G α
  map_id := toPrincipalFunctor_map_id G
  map_comp := toPrincipalFunctor_map_comp G

/-- The comparison functor sends `(U, b, X)` to `(U, b, X)` with the transported
fpqc witness. -/
theorem toPrincipalFunctor_obj (ξ : Torsors.Obj G) :
    (toPrincipalFunctor G).obj ξ = toPrincipalObj G ξ := sorry

/-- The comparison functor lies over `(Sch/S)_fppf`. -/
theorem basedFunctor_w :
    toPrincipalFunctor G ⋙ Principal.forget G = Torsors.forget G := sorry

/-- The based comparison functor of classifying stacks over `(Sch/S)_fppf`. -/
def toPrincipalBasedFunctor :
    (Torsors.stack G).toBasedCategory ⥤ᵇ (Principal.stack G).toBasedCategory where
  toFunctor := toPrincipalFunctor G
  w := basedFunctor_w G

/-- The comparison 1-morphism of stacks `G`-Torsors ⟶ `G`-Principal. -/
def toPrincipal : Torsors.stack G ⟶ Principal.stack G :=
  StackOver.Groupoids.Hom.lift
    (FiberedCategoryOver.Groupoids.ofBasedFunctor (toPrincipalBasedFunctor G))

/-- The comparison 1-morphism preserves the underlying scheme, morphism to `B`,
and action. -/
theorem toPrincipal_obj (ξ : Torsors.Obj G) :
    ((StackOver.Groupoids.Hom.toFunctor (toPrincipal G)).obj ξ).U = ξ.U ∧
      ((StackOver.Groupoids.Hom.toFunctor (toPrincipal G)).obj ξ).b = ξ.b ∧
      ((StackOver.Groupoids.Hom.toFunctor (toPrincipal G)).obj ξ).X = ξ.X := sorry

end AlgebraicGeometry.GroupAlgebraicSpace

namespace AlgebraicGeometry.GroupScheme

variable {S : Scheme.{u}} (G : GroupScheme S)

/-- The comparison 1-morphism `G`-Torsors ⟶ `G`-Principal for a group scheme,
obtained by viewing `G` as a group algebraic space over `S`. -/
def toPrincipal :
    Torsors.stack (toGroupAlgebraicSpace G) ⟶ Principal.stack (toGroupAlgebraicSpace G) :=
  GroupAlgebraicSpace.toPrincipal (toGroupAlgebraicSpace G)

/-- The comparison 1-morphism of a group scheme is the algebraic-space comparison
of `toGroupAlgebraicSpace G`. -/
theorem toPrincipal_eq :
    toPrincipal G = GroupAlgebraicSpace.toPrincipal (toGroupAlgebraicSpace G) :=
  sorry

/-- The comparison functor `G`-Torsors ⟶ `G`-Principal is not essentially
surjective in general. -/
theorem toPrincipal_not_essSurj :
    ∃ (S : Scheme.{u}) (G : GroupScheme S),
      ¬ (StackOver.Groupoids.Hom.toFunctor (toPrincipal G)).EssSurj := sorry

/-- There exist a scheme and a group scheme for which the canonical comparison
from fppf torsors to principal homogeneous spaces is not an equivalence over the
big fppf site. -/
theorem exists_principal_notEquivalent_fppfTorsors :
    ∃ (S : Scheme.{u}) (G : GroupScheme S),
      ¬ BasedFunctor.IsEquivalence
        (StackOver.Groupoids.Hom.toBasedFunctor (toPrincipal G)) := sorry

end AlgebraicGeometry.GroupScheme
