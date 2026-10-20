module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials.InverseImage
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Differentials
import Mathlib.Tactic.CrossRefAttribute

/-!
# Inverse image of relative differentials on topological spaces

The construction is owned for arbitrary continuous functors of sites.  This file gives the
opens-site specialization for a continuous map of topological spaces.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace
open SheafOfModules.RingedSite
open scoped RelativeDerivation

noncomputable section

universe u

namespace TopCat.Sheaf.RelativeDifferentials.InverseImage

variable {X Y : TopCat.{u}} {O₁ O₂ : X.Sheaf CommRingCat.{u}}

/-- The ring-sheaf structure map defining module inverse image along `f`. -/
abbrev structureMap (f : Y ⟶ X) (O : X.Sheaf CommRingCat.{u}) :=
  SheafOfModules.RingedSite.InverseImage.structureMap
    (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
    (Opens.map f) O

/-- The canonical comparison from the inverse image of relative differentials to the relative
differentials of the inverse-image ring map. -/
@[stacks 08RR "opens-site inverse-image differential comparison"]
noncomputable abbrev comparison (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    (SheafOfModules.pullback (structureMap f O₂)).obj
        (TopCat.Sheaf.relativeDifferentials φ) ⟶
      TopCat.Sheaf.relativeDifferentials
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).map φ) :=
  SheafOfModules.RingedSite.RelativeDifferentials.comparison
    (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
    (Opens.map f) φ

/-- The inverse-image comparison on relative differentials is an isomorphism. -/
instance comparison_isIso (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    IsIso (comparison f φ) := sorry

/-- The named inverse of the opens-site inverse-image relative-differentials comparison. -/
@[stacks 08RR "opens-site inverse-image differential comparison inverse"]
noncomputable abbrev comparisonInv (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    TopCat.Sheaf.relativeDifferentials
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).map φ) ⟶
      (SheafOfModules.pullback (structureMap f O₂)).obj
        (TopCat.Sheaf.relativeDifferentials φ) :=
  SheafOfModules.RingedSite.RelativeDifferentials.comparisonInv
    (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
    (Opens.map f) φ

/-- The opens-site inverse-image differential comparison followed by its named inverse is the
identity. -/
@[simp, stacks 08RR "opens-site differential forward-inverse law"]
theorem comparison_hom_inv_id (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    comparison f φ ≫ comparisonInv f φ = 𝟙 _ := sorry

/-- The named inverse followed by the opens-site inverse-image differential comparison is the
identity. -/
@[simp, stacks 08RR "opens-site differential inverse-forward law"]
theorem comparison_inv_hom_id (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    comparisonInv f φ ≫ comparison f φ = 𝟙 _ := sorry

/-- Lemma 17.28.6 (08RR): inverse image commutes canonically with relative differentials. -/
@[stacks 08RR]
noncomputable abbrev iso (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    (SheafOfModules.pullback (structureMap f O₂)).obj
        (TopCat.Sheaf.relativeDifferentials φ) ≅
      TopCat.Sheaf.relativeDifferentials
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).map φ) :=
  SheafOfModules.RingedSite.RelativeDifferentials.comparisonIso
    (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
    (Opens.map f) φ

/-- The forward map of the inverse-image relative-differentials isomorphism is `comparison`. -/
@[stacks 08RR "inverse-image comparison isomorphism hom", simp]
theorem iso_hom (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    (iso f φ).hom = comparison f φ := sorry

/-- The inverse projection of the opens-site inverse-image differential isomorphism is the named
inverse owner. -/
@[stacks 08RR "opens-site inverse-image differential isomorphism inverse", simp]
theorem iso_inv (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    (iso f φ).inv = comparisonInv f φ := sorry

/-- The inverse-image comparison is characterized by the pulled universal derivation. -/
theorem comparison_spec (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    (SheafOfModules.RingedSite.RelativeDifferentials.comparisonDerivation
      (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
      (Opens.map f) φ).IsPullbackDesc (comparison f φ) := sorry

/-- A morphism compatible with the pulled universal derivation is the canonical comparison. -/
theorem eq_comparison (f : Y ⟶ X) (φ : O₁ ⟶ O₂)
    {tau :
      (SheafOfModules.pullback (structureMap f O₂)).obj
          (TopCat.Sheaf.relativeDifferentials φ) ⟶
        TopCat.Sheaf.relativeDifferentials
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).map φ)}
    (h_tau :
      (SheafOfModules.RingedSite.RelativeDifferentials.comparisonDerivation
        (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
        (Opens.map f) φ).IsPullbackDesc tau) :
    tau = comparison f φ := sorry

end TopCat.Sheaf.RelativeDifferentials.InverseImage
