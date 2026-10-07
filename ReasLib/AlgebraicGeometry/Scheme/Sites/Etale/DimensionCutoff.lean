module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme

/-- For every natural number `n`, there is an abelian sheaf on the big étale site
whose sections are zero exactly on schemes of topological Krull dimension less
than `n`, and whose restriction maps along thickenings are isomorphisms. -/
theorem exists_etaleSheaf_dimensionCutoff (n : ℕ) :
    ∃ G : Sheaf Scheme.etaleTopology AddCommGrpCat.{u},
      (∀ X : Scheme.{u}, IsZero (G.obj.obj (op X)) ↔ topologicalKrullDim X < n) ∧
        (∀ {X Y : Scheme.{u}} (i : X ⟶ Y) [IsThickening i],
          IsIso (G.obj.map i.op)) := sorry

end AlgebraicGeometry.Scheme
