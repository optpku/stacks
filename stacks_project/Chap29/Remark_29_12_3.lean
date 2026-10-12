/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong.AmpleFamily
import StacksCheckRecall

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Remark 29.12.3: over a field, the affine line with doubled origin has an ample family of
invertible modules but is not separated. -/
@[stacks 0FXT] #check
  (AlgebraicGeometry.DoubledOrigin.affineLine_hasAmpleFamily_not_isSeparated :
    ∀ (k : Type u) [Field k],
      (∃ L : ℤ → (AlgebraicGeometry.DoubledOrigin.scheme k 1).Modules,
        AlgebraicGeometry.Scheme.Modules.AmpleFamily L) ∧
      ¬ (AlgebraicGeometry.DoubledOrigin.scheme k 1).IsSeparated)

#check
  (AlgebraicGeometry.DoubledOrigin.isTransitionPresentation_iff :
    ∀ (k : Type u) [Field k] (n : ℤ)
        (L : (AlgebraicGeometry.DoubledOrigin.scheme k 1).Modules)
        (e₀ : (AlgebraicGeometry.Scheme.Modules.pullback
            (AlgebraicGeometry.DoubledOrigin.chartMap k 1 0)).obj L ≅
          (SheafOfModules.unit
              (AlgebraicGeometry.DoubledOrigin.affineSpace k 1).ringCatSheaf :
            (AlgebraicGeometry.DoubledOrigin.affineSpace k 1).Modules))
        (e₁ : (AlgebraicGeometry.Scheme.Modules.pullback
            (AlgebraicGeometry.DoubledOrigin.chartMap k 1 1)).obj L ≅
          (SheafOfModules.unit
              (AlgebraicGeometry.DoubledOrigin.affineSpace k 1).ringCatSheaf :
            (AlgebraicGeometry.DoubledOrigin.affineSpace k 1).Modules)),
      AlgebraicGeometry.DoubledOrigin.IsTransitionPresentation k n L e₀ e₁ ↔
        (∀ s : Γ(L, ⊤),
          ∃! fg : AlgebraicGeometry.DoubledOrigin.coordinateRing k 1 ×
              AlgebraicGeometry.DoubledOrigin.coordinateRing k 1,
            AlgebraicGeometry.DoubledOrigin.HasChartValues k L e₀ e₁ s fg.1 fg.2) ∧
        ∀ f g : AlgebraicGeometry.DoubledOrigin.coordinateRing k 1,
          AlgebraicGeometry.DoubledOrigin.IsTransitionPair k n f g ↔
            ∃! s : Γ(L, ⊤),
              AlgebraicGeometry.DoubledOrigin.HasChartValues k L e₀ e₁ s f g)

#check
  (AlgebraicGeometry.DoubledOrigin.isLineBundleFamily_iff :
    ∀ (k : Type u) [Field k]
        (L : ℤ → (AlgebraicGeometry.DoubledOrigin.scheme k 1).Modules),
      AlgebraicGeometry.DoubledOrigin.IsLineBundleFamily k L ↔
        ∃ hL : ∀ n : ℤ, AlgebraicGeometry.Scheme.Modules.Invertible (L n),
          ∃ e₀ : ∀ n : ℤ,
              (AlgebraicGeometry.Scheme.Modules.pullback
                (AlgebraicGeometry.DoubledOrigin.chartMap k 1 0)).obj (L n) ≅
                (SheafOfModules.unit
                    (AlgebraicGeometry.DoubledOrigin.affineSpace k 1).ringCatSheaf :
                  (AlgebraicGeometry.DoubledOrigin.affineSpace k 1).Modules),
            ∃ e₁ : ∀ n : ℤ,
                (AlgebraicGeometry.Scheme.Modules.pullback
                  (AlgebraicGeometry.DoubledOrigin.chartMap k 1 1)).obj (L n) ≅
                  (SheafOfModules.unit
                      (AlgebraicGeometry.DoubledOrigin.affineSpace k 1).ringCatSheaf :
                    (AlgebraicGeometry.DoubledOrigin.affineSpace k 1).Modules),
              ∀ n : ℤ, AlgebraicGeometry.DoubledOrigin.IsTransitionPresentation
                k n (L n) (e₀ n) (e₁ n))

#check
  (AlgebraicGeometry.DoubledOrigin.exists_isLineBundleFamily :
    ∀ (k : Type u) [Field k],
      ∃ L : ℤ → (AlgebraicGeometry.DoubledOrigin.scheme k 1).Modules,
        AlgebraicGeometry.DoubledOrigin.IsLineBundleFamily k L)

section

variable (k : Type u) [Field k]
variable (L : ℤ → (AlgebraicGeometry.DoubledOrigin.scheme k 1).Modules)

#check
  (AlgebraicGeometry.DoubledOrigin.IsLineBundleFamily.exists_chartSections
      (k := k) (L := L) :
    AlgebraicGeometry.DoubledOrigin.IsLineBundleFamily k L →
      ∃ (hInv : ∀ n : ℤ, AlgebraicGeometry.Scheme.Modules.Invertible (L n))
          (e₀ : ∀ n : ℤ,
            (AlgebraicGeometry.Scheme.Modules.pullback
              (AlgebraicGeometry.DoubledOrigin.chartMap k 1 0)).obj (L n) ≅
              (SheafOfModules.unit
                  (AlgebraicGeometry.DoubledOrigin.affineSpace k 1).ringCatSheaf :
                (AlgebraicGeometry.DoubledOrigin.affineSpace k 1).Modules))
          (e₁ : ∀ n : ℤ,
            (AlgebraicGeometry.Scheme.Modules.pullback
              (AlgebraicGeometry.DoubledOrigin.chartMap k 1 1)).obj (L n) ≅
              (SheafOfModules.unit
                  (AlgebraicGeometry.DoubledOrigin.affineSpace k 1).ringCatSheaf :
                (AlgebraicGeometry.DoubledOrigin.affineSpace k 1).Modules))
          (s : Γ(L (1 : ℤ), ⊤)) (t : Γ(L (-1 : ℤ), ⊤)),
        (∀ n : ℤ, AlgebraicGeometry.DoubledOrigin.IsTransitionPresentation
          k n (L n) (e₀ n) (e₁ n)) ∧
        AlgebraicGeometry.DoubledOrigin.HasChartValues
            k (L (1 : ℤ)) (e₀ (1 : ℤ)) (e₁ (1 : ℤ)) s
              1 (AlgebraicGeometry.DoubledOrigin.coordinate k 1 0) ∧
        AlgebraicGeometry.DoubledOrigin.HasChartValues
            k (L (-1 : ℤ)) (e₀ (-1 : ℤ)) (e₁ (-1 : ℤ)) t
              (AlgebraicGeometry.DoubledOrigin.coordinate k 1 0) 1 ∧
        (hInv (1 : ℤ)).sectionNonvanishingOpen s =
            AlgebraicGeometry.DoubledOrigin.chart k 1 0 ∧
        (hInv (-1 : ℤ)).sectionNonvanishingOpen t =
            AlgebraicGeometry.DoubledOrigin.chart k 1 1)

end

#check
  (AlgebraicGeometry.DoubledOrigin.exists_ampleFamily_with_chart_sections :
    ∀ (k : Type u) [Field k],
      ∃ L : ℤ → (AlgebraicGeometry.DoubledOrigin.scheme k 1).Modules,
        AlgebraicGeometry.DoubledOrigin.IsLineBundleFamily k L ∧
        AlgebraicGeometry.Scheme.Modules.AmpleFamily L ∧
          ∃ (hInv : ∀ n : ℤ, AlgebraicGeometry.Scheme.Modules.Invertible (L n))
              (s : Γ(L (1 : ℤ), ⊤)) (t : Γ(L (-1 : ℤ), ⊤)),
            (hInv (1 : ℤ)).sectionNonvanishingOpen s =
                AlgebraicGeometry.DoubledOrigin.chart k 1 0 ∧
            (hInv (-1 : ℤ)).sectionNonvanishingOpen t =
                AlgebraicGeometry.DoubledOrigin.chart k 1 1)
