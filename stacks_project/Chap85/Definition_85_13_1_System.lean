/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap85.Definition_85_13_1_Pullback

/-!
# Simplicial systems in the derived category of abelian sheaves

A system `(K_n, K_φ)` with `K_n` in `D(C_n)` and transition maps
`K_φ : f_φ⁻¹ K_m ⟶ K_n` in `D(C_n)`, functorial in simplex operators up to the
canonical derived inverse-image comparisons.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Functor

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable {C : SimplexCategory → Type u} [∀ n, Category.{v} (C n)]
variable (J : ∀ n, GrothendieckTopology (C n))
variable (fInv : ∀ {m n : SimplexCategory}, (m ⟶ n) →
    Sheaf (J m) AddCommGrpCat.{w} ⥤ Sheaf (J n) AddCommGrpCat.{w})
variable [∀ n, HasSheafify (J n) AddCommGrpCat.{w}]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n), (fInv φ).Additive]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n), PreservesFiniteLimits (fInv φ)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n), PreservesFiniteColimits (fInv φ)]
variable [functoriality : HasAbelianInverseImageFunctoriality J fInv]

/-- A simplicial system of the derived category of abelian sheaves: objects `K_n` in `D(C_n)`
and maps `K_φ : f_φ⁻¹ K_m ⟶ K_n` in `D(C_n)`, unital and functorial after the derived
inverse-image identifications `id ⟶ f_id⁻¹` and `f_φ⁻¹ ∘ f_ψ⁻¹ ⟶ f_{ψ ≫ φ}⁻¹`. -/
structure DerivedAbelianSystem where
  /-- The object `K_n` of `D(C_n)`. -/
  obj : ∀ n : SimplexCategory, DerivedCategory (Sheaf (J n) AddCommGrpCat.{w})
  /-- The transition `K_φ : f_φ⁻¹ K_m ⟶ K_n` in `D(C_n)`. -/
  map : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (derivedInverseImage J fInv φ).obj (obj m) ⟶ obj n
  /-- The identity operator acts by the canonical identity comparison. -/
  map_id : ∀ n : SimplexCategory,
    (derivedInverseImageIdComparisonOf J fInv (functoriality.pullbackIdIso n)).app (obj n) ≫
      map (𝟙 n) = 𝟙 (obj n)
  /-- Transitions respect composition of simplex operators after derived inverse-image
  comparison. -/
  map_comp : ∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
    (derivedInverseImageCompComparisonOf J fInv ψ φ
        (functoriality.pullbackCompIso ψ φ)).app (obj l) ≫
      map (ψ ≫ φ) =
        (fInv φ).mapDerivedCategory.map (map ψ) ≫ map φ

namespace DerivedAbelianSystem

variable {J : ∀ n, GrothendieckTopology (C n)}
variable {fInv : ∀ {m n : SimplexCategory}, (m ⟶ n) →
    Sheaf (J m) AddCommGrpCat.{w} ⥤ Sheaf (J n) AddCommGrpCat.{w}}
variable [∀ n, HasSheafify (J n) AddCommGrpCat.{w}]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n), (fInv φ).Additive]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n), PreservesFiniteLimits (fInv φ)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n), PreservesFiniteColimits (fInv φ)]
variable [functoriality : HasAbelianInverseImageFunctoriality J fInv]

/-- Build a derived abelian system from degreewise objects, transition maps, and the identity
and composition laws. -/
def of (obj : ∀ n : SimplexCategory, DerivedCategory (Sheaf (J n) AddCommGrpCat.{w}))
    (map : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      (derivedInverseImage J fInv φ).obj (obj m) ⟶ obj n)
    (map_id : ∀ n : SimplexCategory,
      (derivedInverseImageIdComparisonOf J fInv (functoriality.pullbackIdIso n)).app (obj n) ≫
        map (𝟙 n) = 𝟙 (obj n))
    (map_comp : ∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
      (derivedInverseImageCompComparisonOf J fInv ψ φ
          (functoriality.pullbackCompIso ψ φ)).app (obj l) ≫
        map (ψ ≫ φ) =
          (fInv φ).mapDerivedCategory.map (map ψ) ≫ map φ) :
    DerivedAbelianSystem J fInv where
  obj := obj
  map := map
  map_id := map_id
  map_comp := map_comp

/-- The identity and composition laws defining a derived abelian system. -/
theorem spec (K : DerivedAbelianSystem J fInv) :
    (∀ n : SimplexCategory,
      (derivedInverseImageIdComparisonOf J fInv (functoriality.pullbackIdIso n)).app (K.obj n) ≫
        K.map (𝟙 n) = 𝟙 (K.obj n)) ∧
      ∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
        (derivedInverseImageCompComparisonOf J fInv ψ φ
            (functoriality.pullbackCompIso ψ φ)).app (K.obj l) ≫
          K.map (ψ ≫ φ) =
            (fInv φ).mapDerivedCategory.map (K.map ψ) ≫ K.map φ :=
  sorry

/-- A morphism of derived abelian systems is a family of maps in each `D(C_n)` commuting with
the transitions `K_φ`. -/
structure Hom (K L : DerivedAbelianSystem J fInv) where
  /-- The component morphism at stage `n`. -/
  app : ∀ n : SimplexCategory, K.obj n ⟶ L.obj n
  /-- Naturality with respect to simplex operators. -/
  naturality : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    K.map φ ≫ app n =
      (fInv φ).mapDerivedCategory.map (app m) ≫ L.map φ

/-- Build a morphism of derived abelian systems from stagewise maps satisfying naturality. -/
def homMk {K L : DerivedAbelianSystem J fInv}
    (app : ∀ n : SimplexCategory, K.obj n ⟶ L.obj n)
    (naturality : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      K.map φ ≫ app n =
        (fInv φ).mapDerivedCategory.map (app m) ≫ L.map φ) :
    Hom K L where
  app := app
  naturality := naturality

/-- The identity morphism of a derived abelian system. -/
def Hom.id (K : DerivedAbelianSystem J fInv) : Hom K K :=
  homMk (fun n ↦ 𝟙 (K.obj n)) sorry

/-- Composition of morphisms of derived abelian systems. -/
def Hom.comp {K L M : DerivedAbelianSystem J fInv}
    (α : Hom K L) (β : Hom L M) : Hom K M :=
  homMk (fun n ↦ α.app n ≫ β.app n) sorry

/-- Stagewise component of a morphism built by `homMk`. -/
theorem homMk_app {K L : DerivedAbelianSystem J fInv}
    (app : ∀ n : SimplexCategory, K.obj n ⟶ L.obj n)
    (naturality : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      K.map φ ≫ app n =
        (fInv φ).mapDerivedCategory.map (app m) ≫ L.map φ)
    (n : SimplexCategory) :
    (homMk app naturality).app n = app n :=
  sorry

/-- A derived abelian system is cartesian when every transition `K_φ` is an isomorphism. -/
class IsCartesian (K : DerivedAbelianSystem J fInv) : Prop where
  /-- Every simplex operator acts by an isomorphism in the derived category. -/
  isIso_map : ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (K.map φ)

/-- Cartesianness is equivalent to every transition map being an isomorphism. -/
theorem isCartesian_iff (K : DerivedAbelianSystem J fInv) :
    IsCartesian K ↔ ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (K.map φ) :=
  sorry

/-- A system whose every transition is an isomorphism is cartesian. -/
instance instIsCartesian_of_isIso
    (K : DerivedAbelianSystem J fInv)
    [h : ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (K.map φ)] :
    IsCartesian K where
  isIso_map := h

end DerivedAbelianSystem

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [IsMorphismDiagram C J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [UnivLE.{max u v, w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n), (abelianInverseImage C J φ).Additive]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n), PreservesFiniteLimits (abelianInverseImage C J φ)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    PreservesFiniteColimits (abelianInverseImage C J φ)]

/-- Case A of Situation 85.3.3: derived abelian systems on the component sites `C_n` with
transitions along `f_φ⁻¹` and the canonical underived identifications of simplex operators. -/
abbrev DerivedAbelianSystemOnComponents :=
  DerivedAbelianSystem (fun n ↦ (J n).toGrothendieck) (fun φ ↦ abelianInverseImage C J φ)

/-- The case A owner is the derived abelian system on component topologies with
`abelianInverseImage` transitions. -/
theorem DerivedAbelianSystemOnComponents_eq :
    DerivedAbelianSystemOnComponents C J =
      DerivedAbelianSystem (fun n ↦ (J n).toGrothendieck)
        (fun φ ↦ abelianInverseImage C J φ) :=
  sorry

end CategoryTheory.SimplicialSites
