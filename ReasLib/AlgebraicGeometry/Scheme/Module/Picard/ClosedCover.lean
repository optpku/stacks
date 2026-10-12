/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Order
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NonvanishingLocus
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic

/-!
# Invertible modules on finite closed covers

This leaf owns the nonvanishing and section-compatibility data needed to glue
invertible scheme modules from a finite closed cover with discrete pairwise
intersections.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open RingedSpace RingedSpace.Hom SheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.ClosedCover

/-- The image in the ambient scheme of the nonvanishing locus of a section on
a closed subscheme. -/
def sectionNonvanishingImage {X : Scheme.{u}} (Z : X.IdealSheafData)
    (L : Z.subscheme.Modules) (s : L.sections) : Set X :=
  Z.subschemeι.base ''
    RingedSpace.sectionNonvanishingLocus Z.subscheme.toRingedSpace L s

/-- A global section on the ambient scheme is compatible with a section on a
closed subscheme through a chosen restriction isomorphism. -/
def sectionCompatible {X : Scheme.{u}} (Z : X.IdealSheafData)
    {M : X.Modules} (t : M.sections) {L : Z.subscheme.Modules} (s : L.sections)
    (e : (Scheme.Modules.pullback Z.subschemeι).obj M ≅ L) : Prop :=
  (Scheme.Modules.pullback Z.subschemeι).map (M.unitHomEquiv.symm t) ≫ e.hom =
    pullbackObjUnitToUnit (toRingCatSheafHom Z.subschemeι.toShHom) ≫ L.unitHomEquiv.symm s

/-- Invertible modules on a finite closed cover of a reduced scheme with discrete pairwise
intersections glue to an invertible module on the ambient scheme. -/
theorem existsInvertibleModule
    {X : Scheme.{u}} [IsReduced X]
    {n : ℕ} (Z : Fin n → X.IdealSheafData)
    (L : (i : Fin n) → (Z i).subscheme.Modules)
    [∀ i : Fin n, Scheme.Modules.Invertible (L i)]
    (h_cover : (⋃ i, ((Z i).support : Set X)) = Set.univ)
    (h_discrete : ∀ i j : Fin n, i ≠ j →
      IsDiscrete (((Z i).support : Set X) ∩ ((Z j).support : Set X))) :
    ∃ (M : X.Modules) (_ : Scheme.Modules.Invertible M),
      Nonempty (∀ i : Fin n, (Scheme.Modules.pullback (Z i).subschemeι).obj M ≅ L i) := sorry

/-- Compatible sections nonvanishing on the pairwise intersections of a finite closed cover
glue together with their invertible modules. -/
theorem existsInvertibleModuleWithSection
    {X : Scheme.{u}} [IsReduced X]
    {n : ℕ} (Z : Fin n → X.IdealSheafData)
    (L : (i : Fin n) → (Z i).subscheme.Modules)
    [∀ i : Fin n, Scheme.Modules.Invertible (L i)]
    (s : ∀ i : Fin n, (L i).sections)
    (h_cover : (⋃ i, ((Z i).support : Set X)) = Set.univ)
    (h_discrete : ∀ i j : Fin n, i ≠ j →
      IsDiscrete (((Z i).support : Set X) ∩ ((Z j).support : Set X)))
    (h_nonvanishing : ∀ i j : Fin n, i ≠ j →
      ((Z i).support : Set X) ∩ ((Z j).support : Set X) ⊆
        sectionNonvanishingImage (Z i) (L i) (s i)) :
    ∃ (M : X.Modules) (_ : Scheme.Modules.Invertible M) (t : M.sections)
      (e : ∀ i : Fin n, (Scheme.Modules.pullback (Z i).subschemeι).obj M ≅ L i),
      ∀ i : Fin n, sectionCompatible (Z i) t (s i) (e i) := sorry

end AlgebraicGeometry.Scheme.Modules.ClosedCover
