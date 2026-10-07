module

public import stacks_project.Chap59.Definition_59_76_1
public import stacks_project.Chap59.Lemma_59_73_6
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe u v

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type v} [CommRing Λ] [IsNoetherianRing Λ]
variable [CompactSpace X] [QuasiSeparatedSpace X]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]

/-- The degree-`b` cohomology of a sheaf placed in degree `b` (as `F[-b]`)
recovers `F`. -/
noncomputable def homologyFunctor_shift_single_iso
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) (b : ℤ) :
    ((DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) b).obj
      (((DerivedCategory.singleFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) 0).obj F)⟦-b⟧)) ≅
      F :=
  ((DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) 0).shiftIso
      (-b) b 0 (neg_add_cancel b)).app
    ((DerivedCategory.singleFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) 0).obj F) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) 0).app F

/-- The induced sheaf morphism `F ⟶ H^b(K)` obtained from a derived map
`F[-b] ⟶ K` by identifying `H^b(F[-b])` with `F`. -/
noncomputable def homology_map_of_shift_single
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)}
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))}
    {b : ℤ}
    (φ :
      ((DerivedCategory.singleFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) 0).obj F)⟦-b⟧ ⟶
      K) :
    F ⟶
      (DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) b).obj K :=
  (homologyFunctor_shift_single_iso F b).inv ≫
    (DerivedCategory.homologyFunctor
      (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) b).map φ

/-- Unfolding of the induced sheaf map `F ⟶ H^b(K)`. -/
theorem homology_map_of_shift_single_eq
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)}
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))}
    {b : ℤ}
    (φ :
      ((DerivedCategory.singleFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) 0).obj F)⟦-b⟧ ⟶
      K) :
    homology_map_of_shift_single φ =
      (homologyFunctor_shift_single_iso F b).inv ≫
        (DerivedCategory.homologyFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) b).map φ := sorry

/-- Surjectivity of `H^b(φ)` is equivalent to an epimorphism `F ⟶ H^b(K)`. -/
theorem epi_homology_map_of_shift_single
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)}
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))}
    {b : ℤ}
    (φ :
      ((DerivedCategory.singleFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) 0).obj F)⟦-b⟧ ⟶
      K)
    (hφ : Epi ((DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) b).map φ)) :
    Epi (homology_map_of_shift_single φ) := sorry

/-- Lemma 59.76.4: on a quasi-compact quasi-separated scheme `X` with Noetherian
ring `Λ`, if `K` is an object of `D(Xₑₜ, Λ)` and `H^b(K)` is constructible, then
there exist affine étale morphisms `j i : U i ⟶ X` such that
`F = ⊕ j_{U i!} underline(Λ)` admits a derived map `F[-b] ⟶ K` inducing a
surjection `F ⟶ H^b(K)` (equivalently, an epimorphism on `H^b` after identifying
`H^b(F[-b])` with `F`). -/
@[stacks 095Z]
theorem exists_finiteExtensionByZeroSum_shift_map_surjective_on_homology
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ) →
        Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))
    (finiteTypeLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ) → Prop)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)))
    (b : ℤ)
    (hHb : IsConstructibleEtaleModule restrict finiteTypeLocallyConstant
      ((DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) b).obj K)) :
    ∃ (n : ℕ) (U : Fin n → Scheme.{u}) (j : ∀ i, U i ⟶ X)
      (hEtale : ∀ i, Etale (j i))
      (hAff : ∀ i, IsAffine (U i))
      (hKan : ∀ i, ∀ G : (U i).Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
        (@etaleRestriction (U i) X (j i) (hEtale i)).op.HasLeftKanExtension G)
      (hSh : ∀ i, HasWeakSheafify (U i).smallEtaleTopology (ModuleCat.{v} Λ))
      (hCoprod : HasCoproduct fun i : Fin n ↦
        (moduleExtensionByZero (j i)).obj
          ((constantSheaf (U i).smallEtaleTopology (ModuleCat.{v} Λ)).obj
            (.of Λ Λ))),
      ∃ (φ :
          ((DerivedCategory.singleFunctor
              (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) 0).obj
            (finiteExtensionByZeroSum U j))⟦-b⟧ ⟶
          K),
        Epi ((DerivedCategory.homologyFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) b).map φ) := sorry

end AlgebraicGeometry.Scheme
