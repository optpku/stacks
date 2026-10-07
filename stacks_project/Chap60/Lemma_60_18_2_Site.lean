module

public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import stacks_project.Chap60.«60_9_1_1_Site»

open AlgebraicGeometry CategoryTheory

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

variable (S : Scheme.{u}) (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)

/-- The object property selecting small crystalline objects whose source over `X` is an
isomorphism, i.e. divided power thickenings of the form `(X, T, δ)`. -/
def isWholeSource :
    ObjectProperty (smallCrystallineSite S I γ h_compatible X x₀) :=
  fun T ↦ IsIso T.obj.1.source.hom

/-- Membership in `isWholeSource` is isomorphism of the source morphism over `X`. -/
theorem isWholeSource_iff
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    isWholeSource S I γ h_compatible X x₀ T ↔ IsIso T.obj.1.source.hom :=
  sorry

/-- The full subcategory of `Cris(X/S)` on whole-source objects `(X, T, δ)`. -/
abbrev chaoticSite :=
  (isWholeSource S I γ h_compatible X x₀).FullSubcategory

/-- The chaotic topology on the whole-source full subcategory of `Cris(X/S)`. -/
abbrev chaoticTopology :
    GrothendieckTopology (chaoticSite S I γ h_compatible X x₀) :=
  GrothendieckTopology.trivial _

/-- The chaotic topology on the whole-source site is the bottom Grothendieck topology. -/
theorem chaoticTopology_eq_bot :
    chaoticTopology S I γ h_compatible X x₀ =
      (⊥ : GrothendieckTopology (chaoticSite S I γ h_compatible X x₀)) :=
  sorry

/-- The fully faithful inclusion of the whole-source subcategory into `Cris(X/S)`. -/
def chaoticInclusion :
    chaoticSite S I γ h_compatible X x₀ ⥤
      smallCrystallineSite S I γ h_compatible X x₀ :=
  ObjectProperty.ι (isWholeSource S I γ h_compatible X x₀)

/-- The inclusion of a whole-source object recovers the underlying small crystalline object. -/
theorem chaoticInclusion_obj
    (T : chaoticSite S I γ h_compatible X x₀) :
    (chaoticInclusion S I γ h_compatible X x₀).obj T = T.obj :=
  sorry

end AlgebraicGeometry.Scheme.Crystalline
