module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.Algebra.Category.ModuleCat.Tor.Independence

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- Two schemes over a common base are Tor independent when their stalk rings at every pair
of compatible points are Tor independent over the corresponding base stalk. -/
def TorIndependentOver {S : Scheme.{u}} (X Y : Over S) : Prop :=
  let X₀ := X.left
  let Y₀ := Y.left
  let f := X.hom
  let g := Y.hom
  let 𝒪X := X₀.presheaf
  let 𝒪Y := Y₀.presheaf
  ∀ (x : X₀) (y : Y₀) (h : f.base x = g.base y),
    ModuleCat.Tor.IsIndependent
      ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
        (ModuleCat.of (𝒪X.stalk x) (𝒪X.stalk x)))
      (h.symm ▸
        (ModuleCat.restrictScalars (g.stalkMap y).hom).obj
          (ModuleCat.of (𝒪Y.stalk y) (𝒪Y.stalk y)))

/-- The pointwise stalk characterization of Tor independence for schemes over a common base. -/
theorem torIndependentOver_iff {S : Scheme.{u}} (X Y : Over S) :
    TorIndependentOver X Y ↔
      let X₀ := X.left
      let Y₀ := Y.left
      let f := X.hom
      let g := Y.hom
      let 𝒪X := X₀.presheaf
      let 𝒪Y := Y₀.presheaf
      ∀ (x : X₀) (y : Y₀) (h : f.base x = g.base y),
        ModuleCat.Tor.IsIndependent
          ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
            (ModuleCat.of (𝒪X.stalk x) (𝒪X.stalk x)))
          (h.symm ▸
            (ModuleCat.restrictScalars (g.stalkMap y).hom).obj
              (ModuleCat.of (𝒪Y.stalk y) (𝒪Y.stalk y))) := sorry

/-- Tor independence over a scheme gives Tor independence of the stalk rings at any pair of
points with the same image in the base. -/
theorem TorIndependentOver.isIndependent {S : Scheme.{u}} {X Y : Over S}
    (hXY : TorIndependentOver X Y) (x : X.left) (y : Y.left)
    (hxy : X.hom.base x = Y.hom.base y) :
    let 𝒪X := X.left.presheaf
    let 𝒪Y := Y.left.presheaf
    ModuleCat.Tor.IsIndependent
      ((ModuleCat.restrictScalars (X.hom.stalkMap x).hom).obj
        (ModuleCat.of (𝒪X.stalk x) (𝒪X.stalk x)))
      (hxy.symm ▸
        (ModuleCat.restrictScalars (Y.hom.stalkMap y).hom).obj
          (ModuleCat.of (𝒪Y.stalk y) (𝒪Y.stalk y))) := sorry

end AlgebraicGeometry.Scheme
