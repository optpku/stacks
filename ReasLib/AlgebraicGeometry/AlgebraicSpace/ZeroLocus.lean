/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Sets.Closeds
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.VanishingH1
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# Zero loci of global sections on algebraic spaces

The vanishing locus of global functions is the image of their scheme-theoretic zero locus
on a chosen étale atlas. Vanishing first cohomology of quasi-coherent modules allows
disjoint closed subsets to be separated by a global function and its translate by one.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The zero locus of a set of global sections is the image of the scheme-theoretic zero
locus of their restrictions to the chosen étale atlas. -/
def zeroLocus {S : Scheme.{u}} (X : AlgebraicSpace S) (s : Set (globalSectionsRing X)) :
    Set (Points X) :=
  Points.mapOfOver (chosenPresentation X).atlas ''
    ((chosenPresentation X).U.left.zeroLocus ((globalSectionsRing_ι X).hom '' s))

/-- The zero locus is the image of the atlas scheme zero locus of the restricted sections. -/
theorem zeroLocus_def {S : Scheme.{u}} (X : AlgebraicSpace S) (s : Set (globalSectionsRing X)) :
    X.zeroLocus s =
      Points.mapOfOver (chosenPresentation X).atlas ''
        ((chosenPresentation X).U.left.zeroLocus ((globalSectionsRing_ι X).hom '' s)) :=
  sorry

/-- A point lies in the zero locus precisely when it lifts to a point of the chosen atlas
where all the restricted sections vanish. -/
theorem mem_zeroLocus_iff {S : Scheme.{u}} (X : AlgebraicSpace S)
    (s : Set (globalSectionsRing X)) (x : Points X) :
    x ∈ X.zeroLocus s ↔
      ∃ u : (chosenPresentation X).U.left,
        Points.mapOfOver (chosenPresentation X).atlas u = x ∧
          u ∈ (chosenPresentation X).U.left.zeroLocus ((globalSectionsRing_ι X).hom '' s) :=
  sorry

/-- The zero locus of a set of global sections is closed in the space of points. -/
theorem isClosed_zeroLocus {S : Scheme.{u}} (X : AlgebraicSpace S)
    (s : Set (globalSectionsRing X)) : IsClosed (X.zeroLocus s) :=
  sorry

/-- The zero locus of a single global function is the image of the zero locus of its
restriction to the chosen atlas. -/
theorem zeroLocus_singleton {S : Scheme.{u}} (X : AlgebraicSpace S) (f : globalSectionsRing X) :
    X.zeroLocus {f} =
      Points.mapOfOver (chosenPresentation X).atlas ''
        ((chosenPresentation X).U.left.zeroLocus {(globalSectionsRing_ι X).hom f}) :=
  sorry

/-- A global function vanishes on every point precisely when its restriction vanishes on
the whole chosen étale atlas. -/
theorem zeroLocus_eq_univ_iff {S : Scheme.{u}} (X : AlgebraicSpace S) (f : globalSectionsRing X) :
    X.zeroLocus {f} = Set.univ ↔
      (chosenPresentation X).U.left.zeroLocus {(globalSectionsRing_ι X).hom f} = Set.univ :=
  sorry

/-- Disjoint closed subsets of a quasi-compact and quasi-separated algebraic space with
vanishing first cohomology on quasi-coherent modules have a global function vanishing on
the first subset whose translate by one vanishes on the second. -/
theorem exists_zeroLocus_subset_of_disjoint {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasVanishingH1 X] (Z₀ Z₁ : TopologicalSpace.Closeds (Points X))
    (hdisj : Disjoint (Z₀ : Set (Points X)) (Z₁ : Set (Points X))) :
    ∃ a : globalSectionsRing X,
      (Z₀ : Set (Points X)) ⊆ X.zeroLocus {a} ∧
        (Z₁ : Set (Points X)) ⊆ X.zeroLocus {a - 1} :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
