module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import stacks_project.Chap92.Lemma_92_4_3
public import stacks_project.Chap92.Lemma_92_11_3
public import stacks_project.Chap92.Remark_92_11_1
public import stacks_project.Chap92.Remark_92_11_5_Tor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Spectral-sequence comparison of `𝒥/𝒥²` with the cotangent complex

Remark 92.11.5 records that the degree-two spectral-sequence differential on `C_{B/A}` is an
isomorphism, that `ker(d)` and `coker(d)` are constant on the surjective subcategory `C'_{B/A}`,
and the resulting identifications `H_n(C_{B/A}, 𝒥/𝒥²) ≅ H^{-n}(L_{B/A})` for `n ≥ 2` and
`H^{-2}(L_{B/A}) ≅ H_0(C_{B/A}, Tor_1^O(𝒥, underline{B}))`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Algebra
open Algebra.PolynomialSite
open Algebra.CotangentComplex
open CommAlgCat.Over.Polynomial
open CommAlgCat.Over.Polynomial.Site
open scoped CategoryTheory

noncomputable section

universe u q q'

namespace Algebra

/-- The object property on polynomial arrows `P ⟶ B` of having a surjective structure map. -/
abbrev isSurjectiveOver (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    ObjectProperty (PolynomialOver A B) :=
  fun X ↦ Function.Surjective (algebraToBase X).algebraMap

/-- Membership in `isSurjectiveOver` is surjectivity of the structure map `P ⟶ B`. -/
theorem isSurjectiveOver_iff {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (X : PolynomialOver A B) :
    isSurjectiveOver A B X ↔ Function.Surjective (algebraToBase X).algebraMap :=
  sorry

/-- The full subcategory of polynomial arrows `P ⟶ B` with surjective structure map. -/
abbrev PolynomialOverSurjective (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :=
  (isSurjectiveOver A B).FullSubcategory

end Algebra

namespace Algebra.PolynomialSite

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q'} (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite A B) (ModuleCat.{u} B))
  (HomotopyCategory.quasiIso ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
    (ComplexShape.up ℤ))]

/-- Derived lower-shriek homology of a sheaf of `B`-modules on `C_{B/A}` in cohomological
degree `k`. -/
def lowerShriekHomology (F : (PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B) (k : ℤ) :
    ModuleCat.{u} B :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} B) k).obj
    (((DerivedCategory.singleFunctor ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B) (0 : ℤ)) ⋙
        Lπ![(PolynomialSite A B), (ModuleCat.{u} B)]).obj F)

/-- Unfolding `lowerShriekHomology` recovers homology of `Lπ!` of the degree-zero single
complex. -/
theorem lowerShriekHomology_eq (F : (PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B) (k : ℤ) :
    lowerShriekHomology A B F k =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} B) k).obj
        (((DerivedCategory.singleFunctor
            ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B) (0 : ℤ)) ⋙
          Lπ![(PolynomialSite A B), (ModuleCat.{u} B)]).obj F) :=
  sorry

/-- Restriction of a sheaf on `C_{B/A}` along the inclusion of the surjective subcategory
`C'_{B/A}`. -/
def restrictSurjective (F : (PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B) :
    ((PolynomialOverSurjective A B)ᵒᵖ)ᵒᵖ ⥤ ModuleCat.{u} B :=
  (isSurjectiveOver A B).ι.op.op ⋙ F

/-- Unfolding `restrictSurjective` recovers precomposition with the double-opposite inclusion. -/
theorem restrictSurjective_eq (F : (PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B) :
    restrictSurjective A B F = (isSurjectiveOver A B).ι.op.op ⋙ F :=
  sorry

/-- Remark 92.11.5 (1). The spectral-sequence differential
`H_2(C_{B/A}, 𝒥/𝒥²) ⟶ H_0(C_{B/A}, Tor_1^O(𝒥, underline{B}))` is an isomorphism. -/
@[stacks 09D5]
theorem conormalHomology_two_isIsomorphic_kernelTorHomology_zero :
    IsIsomorphic (lowerShriekHomology A B (conormalSheaf A B) (-2))
      (lowerShriekHomology A B (kernelTorSheaf A B 1) 0) :=
  sorry

/-- Remark 92.11.5 (2). On the full subcategory `C'_{B/A}` of surjective polynomial arrows
`P ⟶ B`, the kernel of `d : 𝒥/𝒥² ⟶ Ω` is the constant sheaf on `H^{-1}(L_{B/A})`. -/
@[stacks 09D5]
theorem kernel_conormalToOmega_restrict_isIsomorphic_const :
    IsIsomorphic (restrictSurjective A B (kernel (conormalToOmega A B)))
      ((Functor.const _).obj ((cotangentComplex A B).homology (-1))) :=
  sorry

/-- Remark 92.11.5 (3). On the full subcategory `C'_{B/A}` of surjective polynomial arrows
`P ⟶ B`, the cokernel of `d : 𝒥/𝒥² ⟶ Ω` is the constant sheaf on `H^0(L_{B/A})`. -/
@[stacks 09D5]
theorem coker_conormalToOmega_restrict_isIsomorphic_const :
    IsIsomorphic (restrictSurjective A B (cokernel (conormalToOmega A B)))
      ((Functor.const _).obj ((cotangentComplex A B).homology 0)) :=
  sorry

/-- Remark 92.11.5 (4). The kernel of `d : 𝒥/𝒥² ⟶ Ω` on the whole site `C_{B/A}` has vanishing
higher homology. -/
@[stacks 09D5]
theorem kernel_conormalToOmega_higherHomology_isZero {n : ℕ} (hn : 0 < n) :
    IsZero (lowerShriekHomology A B (kernel (conormalToOmega A B)) (-n : ℤ)) :=
  sorry

/-- Remark 92.11.5 (5). The cokernel of `d : 𝒥/𝒥² ⟶ Ω` on the whole site `C_{B/A}` has vanishing
higher homology. -/
@[stacks 09D5]
theorem coker_conormalToOmega_higherHomology_isZero {n : ℕ} (hn : 0 < n) :
    IsZero (lowerShriekHomology A B (cokernel (conormalToOmega A B)) (-n : ℤ)) :=
  sorry

end Algebra.PolynomialSite

namespace Algebra.CotangentComplex

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q'} (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite A B) (ModuleCat.{u} B))
  (HomotopyCategory.quasiIso ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
    (ComplexShape.up ℤ))]

open Algebra.PolynomialSite

/-- The canonical map `H_n(C_{B/A}, 𝒥/𝒥²) ⟶ H_n(C_{B/A}, Ω)` induced by `conormalToOmega`. -/
def conormalToOmega_lowerShriekHomology (n : ℕ) :
    lowerShriekHomology A B (conormalSheaf A B) (-n : ℤ) ⟶
      lowerShriekHomology A B (omegaSheaf A B) (-n : ℤ) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} B) (-n : ℤ)).map
    ((Lπ![(PolynomialSite A B), (ModuleCat.{u} B)]).map
      ((DerivedCategory.singleFunctor
          ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B) (0 : ℤ)).map (conormalToOmega A B)))

/-- The canonical map `conormalToOmega_lowerShriekHomology` is homology of `Lπ!` of the
degree-zero single complex on `conormalToOmega`. -/
theorem conormalToOmega_lowerShriekHomology_fac (n : ℕ) :
    conormalToOmega_lowerShriekHomology A B n =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} B) (-n : ℤ)).map
        ((Lπ![(PolynomialSite A B), (ModuleCat.{u} B)]).map
          ((DerivedCategory.singleFunctor
              ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B) (0 : ℤ)).map
            (conormalToOmega A B))) :=
  sorry

/-- Remark 92.11.5 (6). For `n ≥ 2`, the canonical map
`H_n(C_{B/A}, 𝒥/𝒥²) ⟶ H_n(C_{B/A}, Ω)` is an isomorphism. -/
@[stacks 09D5]
theorem conormalToOmega_lowerShriekHomology_isIso {n : ℕ} (hn : 2 ≤ n) :
    IsIso (conormalToOmega_lowerShriekHomology A B n) :=
  sorry

/-- For `n ≥ 2`, the homology `H_n(C_{B/A}, 𝒥/𝒥²)` identifies with `H^{-n}(L_{B/A})`. -/
theorem conormalHomology_isIsomorphic_cotangentHomology {n : ℕ} (hn : 2 ≤ n) :
    IsIsomorphic (lowerShriekHomology A B (conormalSheaf A B) (-n : ℤ))
      ((cotangentComplex A B).homology (-n : ℤ)) :=
  sorry

/-- Remark 92.11.5 (7). Combined with the degree-two spectral-sequence isomorphism, one obtains
`H^{-2}(L_{B/A}) ≅ H_0(C_{B/A}, Tor_1^O(𝒥, underline{B}))`. -/
@[stacks 09D5]
theorem cotangentHomology_negTwo_isIsomorphic_kernelTorHomology_zero :
    IsIsomorphic ((cotangentComplex A B).homology (-2))
      (lowerShriekHomology A B (kernelTorSheaf A B 1) 0) :=
  sorry

end Algebra.CotangentComplex
