/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Definition_59_71_1
public import stacks_project.Chap59.Definition_59_76_1
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.DerivedCategory
  CategoryTheory.MonoidalCategory CategoryTheory.Sheaf
open scoped CategoryTheory.DerivedCategory.DerivedTensor

universe u v

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type v} [CommRing Λ] [IsNoetherianRing Λ]
variable [CompactSpace X] [QuasiSeparatedSpace X]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [((X.smallEtaleTopology.W :
    MorphismProperty (X.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ))).IsMonoidal]
variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]

-- Local declaration justification (instance diamond): `Sheaf` is a `FullSubcategory`,
-- so `HasZeroMorphisms`/`Preadditive` are synthesized from that embedding, while
-- `DerivedCategory.Q` is typed using `Abelian.toPreadditive` zeros.
attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory
attribute [-instance] Preadditive.fullSubcategory

variable [MonoidalPreadditive (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [∀ (K L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))) (ComplexShape.up ℤ)]
variable [hSheafTensor :
    @DerivedTensor.Right.Has (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) _ _ _ _ _ _]

/-- Lemma 59.76.6: for a scheme `X` and a Noetherian ring `Λ`, if `K` and `L` lie in
`D_c^-(Xₑₜ, Λ)`, then the derived tensor product `K ⊗ᴸ L` again lies in
`D_c^-(Xₑₜ, Λ)`. -/
@[stacks 0961]
theorem etaleConstructible_derivedTensor
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ) →
        Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))
    (finiteTypeLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ) → Prop)
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)))
    (n m : ℤ) (hK_le : K.IsLE n) (hL_le : L.IsLE m)
    (hK : ∀ k : ℤ,
      IsConstructibleEtaleModule restrict finiteTypeLocallyConstant
        ((DerivedCategory.homologyFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) k).obj K))
    (hL : ∀ k : ℤ,
      IsConstructibleEtaleModule restrict finiteTypeLocallyConstant
        ((DerivedCategory.homologyFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) k).obj L)) :
    (∀ k : ℤ,
      IsConstructibleEtaleModule restrict finiteTypeLocallyConstant
        ((DerivedCategory.homologyFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) k).obj (K ⊗ᴸ L))) ∧
      ∃ N : ℤ, (K ⊗ᴸ L).IsLE N :=
  sorry

end AlgebraicGeometry.Scheme
