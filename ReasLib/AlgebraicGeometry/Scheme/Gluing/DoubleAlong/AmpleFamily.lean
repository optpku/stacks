module

public import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong.AffineSpace
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Family
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Ample families on the affine line with doubled origin
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.DoubledOrigin

/-- The polynomial coordinate, viewed as a unit on the punctured affine-line overlap. -/
noncomputable def overlapCoordinateUnit (k : Type u) [Field k] :
    (Localization.Away (coordinate k 1 0))ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (coordinate k 1 0)).unit

/-- A polynomial pair is compatible with the degree-`n` overlap transition when multiplication
by the `n`th integral power of the overlap coordinate carries the first polynomial to the
second. -/
def IsTransitionPair (k : Type u) [Field k] (n : ℤ)
    (f g : coordinateRing k 1) : Prop :=
  ((((overlapCoordinateUnit k) ^ n :
        (Localization.Away (coordinate k 1 0))ˣ) :
      Localization.Away (coordinate k 1 0)) *
    algebraMap (coordinateRing k 1) (Localization.Away (coordinate k 1 0)) f) =
      algebraMap (coordinateRing k 1) (Localization.Away (coordinate k 1 0)) g

/-- A global section has prescribed polynomial values on the two canonical affine charts after
pullback and transport through the supplied chart trivializations. -/
def HasChartValues (k : Type u) [Field k]
    (L : (scheme k 1).Modules)
    (e₀ : (Scheme.Modules.pullback (chartMap k 1 0)).obj L ≅
      (SheafOfModules.unit (affineSpace k 1).ringCatSheaf : (affineSpace k 1).Modules))
    (e₁ : (Scheme.Modules.pullback (chartMap k 1 1)).obj L ≅
      (SheafOfModules.unit (affineSpace k 1).ringCatSheaf : (affineSpace k 1).Modules))
    (s : Γ(L, ⊤)) (f g : coordinateRing k 1) : Prop :=
  (Scheme.Modules.globalSectionsMap e₀.hom).hom
      ((Scheme.Modules.globalSectionsPullback (chartMap k 1 0) L).hom s) =
      (PuncturedAffineSpace.coordinateRingGlobalSectionsIso
        (ULift.{u} (Fin 1)) k).hom f ∧
    (Scheme.Modules.globalSectionsMap e₁.hom).hom
      ((Scheme.Modules.globalSectionsPullback (chartMap k 1 1) L).hom s) =
      (PuncturedAffineSpace.coordinateRingGlobalSectionsIso
        (ULift.{u} (Fin 1)) k).hom g

/-- A chart trivialization presents global sections as precisely the polynomial pairs satisfying
the degree-`n` overlap transition, with uniqueness in both directions. -/
def IsTransitionPresentation (k : Type u) [Field k] (n : ℤ)
    (L : (scheme k 1).Modules)
    (e₀ : (Scheme.Modules.pullback (chartMap k 1 0)).obj L ≅
      (SheafOfModules.unit (affineSpace k 1).ringCatSheaf : (affineSpace k 1).Modules))
    (e₁ : (Scheme.Modules.pullback (chartMap k 1 1)).obj L ≅
      (SheafOfModules.unit (affineSpace k 1).ringCatSheaf : (affineSpace k 1).Modules)) : Prop :=
  (∀ s : Γ(L, ⊤), ∃! fg : coordinateRing k 1 × coordinateRing k 1,
      HasChartValues k L e₀ e₁ s fg.1 fg.2) ∧
    ∀ f g : coordinateRing k 1,
      IsTransitionPair k n f g ↔ ∃! s : Γ(L, ⊤), HasChartValues k L e₀ e₁ s f g

/-- A transition presentation is equivalent to unique chart values for every section together
with unique globalization of every compatible polynomial pair. -/
theorem isTransitionPresentation_iff (k : Type u) [Field k] (n : ℤ)
    (L : (scheme k 1).Modules)
    (e₀ : (Scheme.Modules.pullback (chartMap k 1 0)).obj L ≅
      (SheafOfModules.unit (affineSpace k 1).ringCatSheaf : (affineSpace k 1).Modules))
    (e₁ : (Scheme.Modules.pullback (chartMap k 1 1)).obj L ≅
      (SheafOfModules.unit (affineSpace k 1).ringCatSheaf : (affineSpace k 1).Modules)) :
    IsTransitionPresentation k n L e₀ e₁ ↔
      (∀ s : Γ(L, ⊤), ∃! fg : coordinateRing k 1 × coordinateRing k 1,
        HasChartValues k L e₀ e₁ s fg.1 fg.2) ∧
      ∀ f g : coordinateRing k 1,
        IsTransitionPair k n f g ↔
          ∃! s : Γ(L, ⊤), HasChartValues k L e₀ e₁ s f g := sorry

/-- A degree-indexed family of modules on the doubled affine line is a line-bundle family with
the standard transition presentation when its members are invertible and are trivialized on both
charts with transition exponent equal to the degree. -/
def IsLineBundleFamily (k : Type u) [Field k]
    (L : ℤ → (scheme k 1).Modules) : Prop :=
  ∃ hL : ∀ n : ℤ, Scheme.Modules.Invertible (L n),
    ∃ e₀ : ∀ n : ℤ, (Scheme.Modules.pullback (chartMap k 1 0)).obj (L n) ≅
        (SheafOfModules.unit (affineSpace k 1).ringCatSheaf : (affineSpace k 1).Modules),
      ∃ e₁ : ∀ n : ℤ, (Scheme.Modules.pullback (chartMap k 1 1)).obj (L n) ≅
          (SheafOfModules.unit (affineSpace k 1).ringCatSheaf : (affineSpace k 1).Modules),
        ∀ n : ℤ, IsTransitionPresentation k n (L n) (e₀ n) (e₁ n)

/-- The line-bundle-family condition jointly exposes invertibility, the two chart
trivializations, and their degreewise transition presentations. -/
theorem isLineBundleFamily_iff (k : Type u) [Field k]
    (L : ℤ → (scheme k 1).Modules) :
    IsLineBundleFamily k L ↔
      ∃ hL : ∀ n : ℤ, Scheme.Modules.Invertible (L n),
        ∃ e₀ : ∀ n : ℤ, (Scheme.Modules.pullback (chartMap k 1 0)).obj (L n) ≅
            (SheafOfModules.unit (affineSpace k 1).ringCatSheaf : (affineSpace k 1).Modules),
          ∃ e₁ : ∀ n : ℤ, (Scheme.Modules.pullback (chartMap k 1 1)).obj (L n) ≅
              (SheafOfModules.unit (affineSpace k 1).ringCatSheaf : (affineSpace k 1).Modules),
            ∀ n : ℤ, IsTransitionPresentation k n (L n) (e₀ n) (e₁ n) := sorry

/-- Over a field, the affine line with doubled origin has a degree-indexed line-bundle family
with transition multiplier given by the corresponding integral power of the overlap coordinate. -/
theorem exists_isLineBundleFamily (k : Type u) [Field k] :
    ∃ L : ℤ → (scheme k 1).Modules, IsLineBundleFamily k L := sorry

/-- A standard line-bundle family has degree-one and degree-minus-one sections with chart values
`(1, coordinate)` and `(coordinate, 1)`, whose nonvanishing opens are the two canonical charts. -/
theorem IsLineBundleFamily.exists_chartSections {k : Type u} [Field k]
    {L : ℤ → (scheme k 1).Modules} (hL : IsLineBundleFamily k L) :
    ∃ (hInv : ∀ n : ℤ, Scheme.Modules.Invertible (L n))
        (e₀ : ∀ n : ℤ, (Scheme.Modules.pullback (chartMap k 1 0)).obj (L n) ≅
          (SheafOfModules.unit (affineSpace k 1).ringCatSheaf : (affineSpace k 1).Modules))
        (e₁ : ∀ n : ℤ, (Scheme.Modules.pullback (chartMap k 1 1)).obj (L n) ≅
          (SheafOfModules.unit (affineSpace k 1).ringCatSheaf : (affineSpace k 1).Modules))
        (s : Γ(L (1 : ℤ), ⊤)) (t : Γ(L (-1 : ℤ), ⊤)),
      (∀ n : ℤ, IsTransitionPresentation k n (L n) (e₀ n) (e₁ n)) ∧
        HasChartValues k (L (1 : ℤ)) (e₀ (1 : ℤ)) (e₁ (1 : ℤ)) s
          1 (coordinate k 1 0) ∧
        HasChartValues k (L (-1 : ℤ)) (e₀ (-1 : ℤ)) (e₁ (-1 : ℤ)) t
          (coordinate k 1 0) 1 ∧
        (hInv (1 : ℤ)).sectionNonvanishingOpen s = chart k 1 0 ∧
        (hInv (-1 : ℤ)).sectionNonvanishingOpen t = chart k 1 1 := sorry

/-- Every standard degree-indexed line-bundle family on the doubled affine line is an ample
family of invertible modules. -/
theorem IsLineBundleFamily.ampleFamily {k : Type u} [Field k]
    {L : ℤ → (scheme k 1).Modules} (hL : IsLineBundleFamily k L) :
    Scheme.Modules.AmpleFamily L := sorry

/-- The affine line with doubled origin admits an ample family indexed by `ℤ`, with sections in
degrees `1` and `-1` whose nonvanishing opens are the two canonical affine charts. -/
theorem exists_ampleFamily_with_chart_sections (k : Type u) [Field k] :
    ∃ L : ℤ → (scheme k 1).Modules,
      IsLineBundleFamily k L ∧ Scheme.Modules.AmpleFamily L ∧
        ∃ (hInv : ∀ n : ℤ, Scheme.Modules.Invertible (L n))
            (s : Γ(L (1 : ℤ), ⊤)) (t : Γ(L (-1 : ℤ), ⊤)),
          (hInv (1 : ℤ)).sectionNonvanishingOpen s = chart k 1 0 ∧
          (hInv (-1 : ℤ)).sectionNonvanishingOpen t = chart k 1 1 := sorry

/-- Over a field, the affine line with doubled origin has an ample family of invertible modules
but is not separated. -/
theorem affineLine_hasAmpleFamily_not_isSeparated (k : Type u) [Field k] :
    (∃ L : ℤ → (scheme k 1).Modules, Scheme.Modules.AmpleFamily L) ∧
    ¬ (scheme k 1).IsSeparated := sorry

end AlgebraicGeometry.DoubledOrigin
