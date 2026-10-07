module

public import stacks_project.Chap59.Definition_59_76_1
public import stacks_project.Chap59.Lemma_59_73_6
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import ReasLib.CategoryTheory.Monoidal.Flat
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.Sheaf

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

/-- The localization functor applied to a cochain complex of étale `Λ`-module sheaves. -/
noncomputable def etaleModuleDerivedQ
    (C : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ℤ) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) :=
  DerivedCategory.Q.obj C

/-- Unfolding of `etaleModuleDerivedQ`. -/
theorem etaleModuleDerivedQ_eq
    (C : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ℤ) :
    etaleModuleDerivedQ C = DerivedCategory.Q.obj C := sorry

/-- A sheaf of `Λ`-modules on `Xₑₜ` is isomorphic to a finite coproduct of
`j_{U!} underline(Λ)` for affine étale `U`. -/
def IsFiniteAffineEtaleExtensionByZeroSum
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) : Prop :=
  ∃ (n : ℕ) (U : Fin n → Scheme.{u}) (j : ∀ i, U i ⟶ X)
    (hEtale : ∀ i, Etale (j i))
    (_ : ∀ i, IsAffine (U i))
    (_ : ∀ i, ∀ G : (U i).Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
      (@etaleRestriction (U i) X (j i) (hEtale i)).op.HasLeftKanExtension G)
    (_ : ∀ i, HasWeakSheafify (U i).smallEtaleTopology (ModuleCat.{v} Λ))
    (_ : HasCoproduct fun i : Fin n ↦
      (moduleExtensionByZero (j i)).obj
        ((constantSheaf (U i).smallEtaleTopology (ModuleCat.{v} Λ)).obj (.of Λ Λ))),
    Nonempty (F ≅ finiteExtensionByZeroSum U j)

/-- Unfolding of the affine étale finite-extension-by-zero-sum predicate. -/
theorem isFiniteAffineEtaleExtensionByZeroSum_iff
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) :
    IsFiniteAffineEtaleExtensionByZeroSum F ↔
      ∃ (n : ℕ) (U : Fin n → Scheme.{u}) (j : ∀ i, U i ⟶ X)
        (hEtale : ∀ i, Etale (j i))
        (_ : ∀ i, IsAffine (U i))
        (_ : ∀ i, ∀ G : (U i).Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
          (@etaleRestriction (U i) X (j i) (hEtale i)).op.HasLeftKanExtension G)
        (_ : ∀ i, HasWeakSheafify (U i).smallEtaleTopology (ModuleCat.{v} Λ))
        (_ : HasCoproduct fun i : Fin n ↦
          (moduleExtensionByZero (j i)).obj
            ((constantSheaf (U i).smallEtaleTopology (ModuleCat.{v} Λ)).obj
              (.of Λ Λ))),
        Nonempty (F ≅ finiteExtensionByZeroSum U j) := sorry

/-- Lemma 59.76.5 (1): for a quasi-compact quasi-separated scheme `X` and a Noetherian
ring `Λ`, an object `K` of `D^-(Xₑₜ, Λ)` lies in `D_c(Xₑₜ, Λ)` if and only if it is
isomorphic in the derived category to a strictly bounded-above complex whose terms are
finite coproducts of `j_{U!} underline(Λ)` with `U` affine étale. -/
@[stacks 0960]
theorem mem_etaleConstructible_iff_iso_jShriekSum
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ) →
        Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))
    (finiteTypeLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ) → Prop)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)))
    (n : ℤ) [K.IsLE n] :
    (∀ k : ℤ,
        IsConstructibleEtaleModule restrict finiteTypeLocallyConstant
          ((DerivedCategory.homologyFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) k).obj K)) ↔
      ∃ C : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ℤ,
        C.IsStrictlyLE n ∧
          (∀ i : ℤ, IsFiniteAffineEtaleExtensionByZeroSum (C.X i)) ∧
            Nonempty (K ≅ etaleModuleDerivedQ C) := sorry

/-- Lemma 59.76.5 (2): equivalently, `K` is isomorphic in the derived category to a
strictly bounded-above complex of flat constructible sheaves of `Λ`-modules. -/
@[stacks 0960]
theorem mem_etaleConstructible_iff_iso_flatConstructible
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ) →
        Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))
    (finiteTypeLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ) → Prop)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)))
    (n : ℤ) [K.IsLE n] :
    (∀ k : ℤ,
        IsConstructibleEtaleModule restrict finiteTypeLocallyConstant
          ((DerivedCategory.homologyFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) k).obj K)) ↔
      ∃ C : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ℤ,
        C.IsStrictlyLE n ∧
          (∀ i : ℤ,
            IsConstructibleEtaleModule restrict finiteTypeLocallyConstant (C.X i) ∧
              IsFlat (C.X i)) ∧
            Nonempty (K ≅ etaleModuleDerivedQ C) := sorry

end AlgebraicGeometry.Scheme
