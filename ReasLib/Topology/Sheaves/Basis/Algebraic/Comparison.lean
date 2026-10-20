module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import ReasLib.Topology.Sheaves.Basis.Algebraic.Basic
public import ReasLib.Topology.Sheaves.Basis.Comparison

/-!
# Algebraic sheaves on a topological basis

This module compares basis-cover sheaves detected by an underlying `Type`-valued functor with
sheaves on the induced basis site and then with sheaves on the ambient topological space.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace

noncomputable section

universe u v w t

variable {X : TopCat.{u}}
variable {C : Type v} [Category.{w} C]
variable {F : C ⥤ Type t} [IsAlgebraicStructure C F]
variable {B : Set (Opens X)}
variable [HasLimitsOfSize.{u, u} C] [PreservesLimitsOfSize.{u, u} F]

namespace AlgebraicBasisSheaf

/-- The underlying-set basis-cover condition for an algebraic presheaf is equivalent to the
canonical `C`-valued sheaf condition for the topology induced on the basis. -/
theorem isBasisSheaf_iff_isSheaf (hB : Opens.IsBasis B)
    (ℱ : (BasisOpen B)ᵒᵖ ⥤ C) :
    Presheaf.IsBasisSheaf (ℱ ⋙ F) ↔
      Presheaf.IsSheaf (basisGrothendieckTopology B) ℱ := sorry

/-- Algebraic basis sheaves defined through their underlying sets form the canonical category of
`C`-valued sheaves on the induced basis site. -/
public noncomputable def algebraicBasisSheafEquivBasisSiteSheaf
    (hB : Opens.IsBasis B) :
    AlgebraicBasisSheaf F B ≌ BasisSiteSheaf C B :=
  ObjectProperty.fullSubcategoryCongr
    (funext fun ℱ ↦ propext (isBasisSheaf_iff_isSheaf hB ℱ))

/-- The canonical comparison equivalence between algebraic sheaves on a topological basis and
`C`-valued sheaves on the whole space. -/
public noncomputable def algebraicBasisSheafComparisonEquiv (hB : Opens.IsBasis B) :
    AlgebraicBasisSheaf F B ≌ TopCat.Sheaf C X :=
  (algebraicBasisSheafEquivBasisSiteSheaf hB).trans
    (BasisSiteSheaf.basisSiteSheafComparisonEquiv (C := C) hB)

/-- The canonical extension to all opens of an algebraic sheaf given on a topological basis. -/
noncomputable abbrev extend (ℱ : AlgebraicBasisSheaf F B) (hB : Opens.IsBasis B) :
    TopCat.Sheaf C X :=
  (algebraicBasisSheafComparisonEquiv hB).functor.obj ℱ

end AlgebraicBasisSheaf
