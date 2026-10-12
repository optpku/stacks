/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.CategoryTheory.Sites.Topos.Morphism

/-!
# Sheaf systems on a simplex-indexed family of topoi

The category of systems `(F_n, F(φ))` consisting of a sheaf on each stage topos `Sh(C n)`
and a transition `F(φ) : F_m ⟶ f_{φ,*} F_n` for each simplex operator, unital and functorial
in `φ` after the canonical pushforward identifications.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

/-- Functoriality of sheaf pushforwards along a family of morphisms of topoi indexed by simplex
operators: the identifications `f_id,* ≅ 𝟭` and `f_{ψ,*} ∘ f_{φ,*} ≅ f_{ψ ≫ φ,*}`. -/
class HasPushforwardFunctoriality
    {C : SimplexCategory → Type u} [∀ n, Category.{v} (C n)]
    (J : ∀ n, GrothendieckTopology (C n))
    (fHom : ∀ {m n : SimplexCategory}, (m ⟶ n) → MorphismOfTopoiIn (J m) (J n)) where
  /-- Canonical identification `(f_id)_* ≅ 𝟭`. -/
  pushforwardIdIso (n : SimplexCategory) :
    (fHom (𝟙 n)).pushforward ≅ 𝟭 (Sheaf (J n) (Type w))
  /-- Canonical identification `(f_ψ)_* ∘ (f_φ)_* ≅ (f_{ψ ≫ φ})_*`. -/
  pushforwardCompIso {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (fHom φ).pushforward ⋙ (fHom ψ).pushforward ≅ (fHom (ψ ≫ φ)).pushforward

/-- A system of sheaves on the stages of a simplex-indexed family of topoi, with transition maps
`F(φ) : F_m ⟶ f_{φ,*} F_n` in `Sh(C m)`, equivalently `f_φ⁻¹ F_m ⟶ F_n` in `Sh(C n)`, unital and
functorial in simplex operators. -/
structure SheafSystem
    {C : SimplexCategory → Type u} [∀ n, Category.{v} (C n)]
    (J : ∀ n, GrothendieckTopology (C n))
    (fHom : ∀ {m n : SimplexCategory}, (m ⟶ n) → MorphismOfTopoiIn (J m) (J n))
    [functoriality : HasPushforwardFunctoriality J fHom] where
  /-- The sheaf `F_n` on the stage topos `Sh(C n)`. -/
  obj : ∀ n : SimplexCategory, Sheaf (J n) (Type w)
  /-- The pushforward-form transition `F(φ) : F_m ⟶ f_{φ,*} F_n`. -/
  map : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    obj m ⟶ (fHom φ).pushforward.obj (obj n)
  /-- The identity operator acts by the canonical identity comparison. -/
  map_id : ∀ n : SimplexCategory,
    map (𝟙 n) = (functoriality.pushforwardIdIso n).inv.app (obj n)
  /-- Transitions respect composition of simplex operators after pushforward comparison. -/
  map_comp : ∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
    map (ψ ≫ φ) =
      map ψ ≫ (fHom ψ).pushforward.map (map φ) ≫
        (functoriality.pushforwardCompIso ψ φ).hom.app (obj n)

namespace SheafSystem

variable {C : SimplexCategory → Type u} [∀ n, Category.{v} (C n)]
variable {J : ∀ n, GrothendieckTopology (C n)}
variable {fHom : ∀ {m n : SimplexCategory}, (m ⟶ n) → MorphismOfTopoiIn (J m) (J n)}
variable [functoriality : HasPushforwardFunctoriality J fHom]

/-- Build a sheaf system from degreewise sheaves, transition maps, and the identity and
composition laws. -/
def of (obj : ∀ n : SimplexCategory, Sheaf (J n) (Type w))
    (map : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      obj m ⟶ (fHom φ).pushforward.obj (obj n))
    (map_id : ∀ n : SimplexCategory,
      map (𝟙 n) = (functoriality.pushforwardIdIso n).inv.app (obj n))
    (map_comp : ∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
      map (ψ ≫ φ) =
        map ψ ≫ (fHom ψ).pushforward.map (map φ) ≫
          (functoriality.pushforwardCompIso ψ φ).hom.app (obj n)) :
    SheafSystem J fHom where
  obj := obj
  map := map
  map_id := map_id
  map_comp := map_comp

/-- The identity and composition laws defining a sheaf system. -/
theorem spec (S : SheafSystem J fHom) :
    (∀ n : SimplexCategory,
      S.map (𝟙 n) = (functoriality.pushforwardIdIso n).inv.app (S.obj n)) ∧
    ∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
      S.map (ψ ≫ φ) =
        S.map ψ ≫ (fHom ψ).pushforward.map (S.map φ) ≫
          (functoriality.pushforwardCompIso ψ φ).hom.app (S.obj n) :=
  sorry

/-- The inverse-image form of a transition, obtained as the adjunction mate
`f_φ⁻¹ F_m ⟶ F_n` of `F(φ) : F_m ⟶ f_{φ,*} F_n`. -/
def mapInverseImage (S : SheafSystem J fHom) {m n : SimplexCategory} (φ : m ⟶ n) :
    (fHom φ).inverseImage.obj (S.obj m) ⟶ S.obj n :=
  ((fHom φ).adjunction.homEquiv (S.obj m) (S.obj n)).symm (S.map φ)

/-- The adjunction mate of `mapInverseImage` recovers the pushforward-form transition. -/
theorem mapInverseImage_homEquiv (S : SheafSystem J fHom)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    ((fHom φ).adjunction.homEquiv (S.obj m) (S.obj n)) (S.mapInverseImage φ) = S.map φ :=
  sorry

/-- A morphism of sheaf systems is a family of sheaf morphisms commuting with the transitions. -/
structure Hom (S T : SheafSystem J fHom) where
  /-- The component sheaf morphism at stage `n`. -/
  app : ∀ n : SimplexCategory, S.obj n ⟶ T.obj n
  /-- Naturality with respect to simplex operators in pushforward form. -/
  naturality : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    S.map φ ≫ (fHom φ).pushforward.map (app n) = app m ≫ T.map φ

/-- Build a morphism of sheaf systems from stagewise sheaf maps satisfying naturality. -/
def homMk {S T : SheafSystem J fHom} (app : ∀ n : SimplexCategory, S.obj n ⟶ T.obj n)
    (naturality : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      S.map φ ≫ (fHom φ).pushforward.map (app n) = app m ≫ T.map φ) :
    Hom S T where
  app := app
  naturality := naturality

/-- The identity morphism of a sheaf system. -/
def Hom.id (S : SheafSystem J fHom) : Hom S S :=
  homMk (fun n ↦ 𝟙 (S.obj n)) sorry

/-- Composition of morphisms of sheaf systems. -/
def Hom.comp {S T U : SheafSystem J fHom} (α : Hom S T) (β : Hom T U) : Hom S U :=
  homMk (fun n ↦ α.app n ≫ β.app n) sorry

/-- The stagewise component of `homMk app naturality` is `app`. -/
theorem homMk_app {S T : SheafSystem J fHom} (app : ∀ n : SimplexCategory, S.obj n ⟶ T.obj n)
    (naturality : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      S.map φ ≫ (fHom φ).pushforward.map (app n) = app m ≫ T.map φ)
    (n : SimplexCategory) :
    (homMk app naturality).app n = app n :=
  sorry

/-- The category of sheaf systems on the family of topoi `(Sh(C n), f_φ)`. -/
instance category : Category (SheafSystem J fHom) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

end SheafSystem

end CategoryTheory.SimplicialSites
