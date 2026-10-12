/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap61.Lemma_61_27_2_Comparison
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 61.27.5

The derived category of bounded-above complexes of sheaves of `Λ`-modules on
`X.ProEt` with constructible cohomology is closed under derived tensor.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory
  CategoryTheory.Sheaf
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
variable [∀ Y : Scheme.{u}, HasWeakSheafify (ProEt.topology Y) (ModuleCat.{w} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.ProEt),
    HasWeakSheafify ((ProEt.topology Y).over U) (ModuleCat.{w} Λ)]
variable [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ),
    (ProEt.baseChange f).op.HasLeftKanExtension P]
variable [Abelian (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ))]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ))]
variable [MonoidalCategory (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ))]

-- Local declaration justification (instance diamond): `Sheaf` is a `FullSubcategory`,
-- so `HasZeroMorphisms`/`Preadditive` are synthesized from that embedding, while
-- derived tensor and `mapDerivedCategory` are typed using `Abelian.toPreadditive`.
attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory
attribute [-instance] Preadditive.fullSubcategory

variable [MonoidalPreadditive (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ))]
variable [∀ (K L : CochainComplex (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ))) (ComplexShape.up ℤ)]
variable [h_derivedTensor :
    @DerivedTensor.Right.Has (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ)) _ _ _ _ _ _]

/-- Lemma 61.27.5: for a scheme `X` and a Noetherian ring `Λ`, if `K` and `L` lie in
`D_c^-(X.ProEt, Λ)`, then the derived tensor product `K ⊗ᴸ L` again lies in
`D_c^-(X.ProEt, Λ)`. -/
@[stacks 09BQ]
theorem constructibleProEtaleModule_derivedTensor
    (K L : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ)))
    (hK : DerivedCategory.IsBoundedAbove K) (hL : DerivedCategory.IsBoundedAbove L)
    (hK_c : DerivedCategory.cohomologyIn (constructibleProEtaleModule X Λ) K)
    (hL_c : DerivedCategory.cohomologyIn (constructibleProEtaleModule X Λ) L) :
    DerivedCategory.IsBoundedAbove (K ⊗ᴸ L) ∧
      DerivedCategory.cohomologyIn (constructibleProEtaleModule X Λ) (K ⊗ᴸ L) :=
  sorry

/-- The derived tensor of two objects of `D_c^-(X.ProEt, Λ)` is bounded above. -/
theorem constructibleProEtaleModule_derivedTensor_isBoundedAbove
    (K L : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ)))
    (hK : DerivedCategory.IsBoundedAbove K) (hL : DerivedCategory.IsBoundedAbove L)
    (hK_c : DerivedCategory.cohomologyIn (constructibleProEtaleModule X Λ) K)
    (hL_c : DerivedCategory.cohomologyIn (constructibleProEtaleModule X Λ) L) :
    DerivedCategory.IsBoundedAbove (K ⊗ᴸ L) :=
  sorry

/-- The derived tensor of two objects of `D_c^-(X.ProEt, Λ)` has constructible cohomology. -/
theorem constructibleProEtaleModule_derivedTensor_cohomologyIn
    (K L : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ)))
    (hK : DerivedCategory.IsBoundedAbove K) (hL : DerivedCategory.IsBoundedAbove L)
    (hK_c : DerivedCategory.cohomologyIn (constructibleProEtaleModule X Λ) K)
    (hL_c : DerivedCategory.cohomologyIn (constructibleProEtaleModule X Λ) L) :
    DerivedCategory.cohomologyIn (constructibleProEtaleModule X Λ) (K ⊗ᴸ L) :=
  sorry

/-- Each cohomology sheaf of the derived tensor of two objects of `D_c^-(X.ProEt, Λ)` is
constructible. -/
theorem constructibleProEtaleModule_derivedTensor_homology
    (K L : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ)))
    (hK : DerivedCategory.IsBoundedAbove K) (hL : DerivedCategory.IsBoundedAbove L)
    (hK_c : DerivedCategory.cohomologyIn (constructibleProEtaleModule X Λ) K)
    (hL_c : DerivedCategory.cohomologyIn (constructibleProEtaleModule X Λ) L)
    (k : ℤ) :
    constructibleProEtaleModule X Λ
      ((DerivedCategory.homologyFunctor _ k).obj (K ⊗ᴸ L)) :=
  sorry

end AlgebraicGeometry.Scheme

end

end
