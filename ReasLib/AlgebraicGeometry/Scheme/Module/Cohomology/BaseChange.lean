module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiCompact
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiSeparated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.RingTheory.Flatness.LocallyFree.Finite

/-!
# Base Change for Scheme Cohomology

This leaf records affine-base cohomology comparisons after extension of scalars
along flat and finite locally free algebras.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {X Y : Scheme.{u}}

/-- In a cartesian square over `Spec A` and `Spec B`, extension of scalars along a flat
`A`-algebra carries the cohomology of a quasicoherent module to the cohomology of its
pullback when the structure morphism is quasi-compact and quasi-separated. -/
theorem cohomology_baseChange_of_flat
    (f : X ⟶ Spec (CommRingCat.of A))
    (g : Y ⟶ Spec (CommRingCat.of B))
    (h : Y ⟶ X)
    (sq : IsPullback h g f (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    [Module.Flat A B] [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] (i : ℕ) :
    IsIsomorphic
      ((ModuleCat.extendScalars (algebraMap A B)).obj (cohomology f F i))
      (cohomology g ((Scheme.Modules.pullback h).obj F) i) := sorry

/-- In a cartesian square over `Spec A` and `Spec B`, extension of scalars along a finite
locally free `A`-algebra carries the cohomology of a quasicoherent module to the cohomology of
its pullback. -/
theorem cohomology_baseChange_of_finiteLocallyFree
    (f : X ⟶ Spec (CommRingCat.of A))
    (g : Y ⟶ Spec (CommRingCat.of B))
    (h : Y ⟶ X)
    (sq : IsPullback h g f (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    [Module.FiniteLocallyFree A B]
    (F : X.Modules) [F.IsQuasicoherent] (i : ℕ) :
    IsIsomorphic
      ((ModuleCat.extendScalars (algebraMap A B)).obj (cohomology f F i))
      (cohomology g ((Scheme.Modules.pullback h).obj F) i) := sorry

end AlgebraicGeometry.Scheme.Hom
