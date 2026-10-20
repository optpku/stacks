module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation

/-!
# Pullbacks, binary products, and terminal objects in chosen big-site slices

This file records pullback properties of a chosen big-site carrier and of its
slice categories, together with binary products and the canonical terminal object of a slice.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.ChosenBigSite

variable {P : Precoverage Scheme.{u}} (𝒮 : ChosenBigSite.{u, v} P)
  (S : 𝒮.carrier)

/-- The carrier of a chosen big-site presentation has pullbacks. -/
theorem carrierHasPullbacks : Limits.HasPullbacks 𝒮.carrier :=
  𝒮.hasPullbacks

/-- The scheme functor of a chosen big-site presentation preserves pullbacks. -/
theorem toSchemePreservesPullbacks :
    Limits.PreservesLimitsOfShape Limits.WalkingCospan 𝒮.toScheme :=
  𝒮.spec.toScheme_preservesPullbacks

/-- The functor from the slice of a chosen big-site carrier to schemes. -/
abbrev sliceToScheme : Over S ⥤ Scheme.{u} :=
  Over.forget S ⋙ 𝒮.toScheme

/-- The slice over an object of a chosen big-site carrier has pullbacks. -/
theorem sliceHasPullbacks : Limits.HasPullbacks (Over S) := sorry

/-- The slice over an object of a chosen big-site carrier has binary products,
constructed from pullbacks in the carrier. -/
@[implicit_reducible]
def sliceHasBinaryProducts : Limits.HasBinaryProducts (Over S) :=
  @Over.ConstructProducts.over_binaryProduct_of_pullback 𝒮.carrier _ 𝒮.hasPullbacks S

/-- The functor from a chosen big-site slice to schemes preserves pullbacks. -/
theorem sliceToSchemePreservesPullbacks :
    Limits.PreservesLimitsOfShape Limits.WalkingCospan (sliceToScheme 𝒮 S) := sorry

/-- The identity morphism of an object in a chosen big-site carrier is terminal
in the slice over that object. -/
noncomputable def sliceIdentityTerminal :
    Limits.IsTerminal (Over.mk (𝟙 S) : Over S) :=
  Over.mkIdTerminal

end AlgebraicGeometry.ChosenBigSite
