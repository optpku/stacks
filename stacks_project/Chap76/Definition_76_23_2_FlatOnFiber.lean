module

public import stacks_project.Chap76.Lemma_76_23_1

/-!
# Fibrewise relative flatness of modules on algebraic spaces

In a triangle `X ⟶ Y ⟶ Z` of algebraic spaces, a module on `X` is flat at a point of
`|X|` on the fibre over `Z` relative to the fibre of `Y` when the field-valued fibre
condition of Lemma 76.23.1 holds. The structure sheaf specializations record the same
condition for `𝒪_X`, pointwise or at every point over a fixed `z ∈ |Z|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}

namespace Modules

/-- The restriction of `F` to the fibre of `X` over the image of `x` in `|Z|` is flat at
`x` over the fibre of `Y`, tested on the field-valued fibre product. -/
abbrev flatOnFiberAt (F : X.Modules) (f : X ⟶ Y) (h : Y ⟶ Z) (x : Points X) : Prop :=
  flatOnFiberAt_field F f h x

/-- For a quasi-coherent module, fibrewise relative flatness at `x` is equivalent to the
geometric-point fibre-stalk condition. -/
theorem flatOnFiberAt_iff_stalk (F : X.Modules) [F.IsQuasicoherent] (f : X ⟶ Y)
    (h : Y ⟶ Z) (x : Points X) :
    flatOnFiberAt F f h x ↔ flatOnFiberAt_stalk F f h x :=
  sorry

/-- For a quasi-coherent module, fibrewise relative flatness at `x` is equivalent to the
étale scheme-presentation condition. -/
theorem flatOnFiberAt_iff_etale (F : X.Modules) [F.IsQuasicoherent] (f : X ⟶ Y)
    (h : Y ⟶ Z) (x : Points X) :
    flatOnFiberAt F f h x ↔ flatOnFiberAt_etale F f h x :=
  sorry

end Modules

/-- The fibre of `X` over the image of `x` in `|Z|` is flat at `x` over the fibre of `Y`. -/
def fiberFlatAt (f : X ⟶ Y) (h : Y ⟶ Z) (x : Points X) : Prop :=
  Modules.flatOnFiberAt (SheafOfModules.unit (structureSheaf X)) f h x

/-- `fiberFlatAt` is fibrewise relative flatness of `𝒪_X`. -/
theorem fiberFlatAt_iff (f : X ⟶ Y) (h : Y ⟶ Z) (x : Points X) :
    fiberFlatAt f h x ↔
      Modules.flatOnFiberAt (SheafOfModules.unit (structureSheaf X)) f h x :=
  sorry

/-- The fibre of `X` over `z` is flat over the fibre of `Y` over `z`. -/
def fiberFlatOver (f : X ⟶ Y) (h : Y ⟶ Z) (z : Points Z) : Prop :=
  ∀ x : Points X, Points.map (f ≫ h) x = z → fiberFlatAt f h x

/-- `fiberFlatOver` is fibrewise relative flatness of `𝒪_X` at every point of `|X|` over
`z`. -/
theorem fiberFlatOver_iff (f : X ⟶ Y) (h : Y ⟶ Z) (z : Points Z) :
    fiberFlatOver f h z ↔
      ∀ x : Points X, Points.map (f ≫ h) x = z → fiberFlatAt f h x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
