/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf

/-!
# Indexed covers and refinement maps

Schemes over a fixed test scheme, their pairwise and triple fibre products,
and the canonical projections and maps induced by refinements.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The member `T_i` of an indexed family over `T`, viewed as a scheme over `S`. -/
def coverOver {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left) (i : ι) :
    Over S :=
  Over.mk ((family i).hom ≫ T.hom)

/-- The structure morphism `T_i ⟶ T` of a covering member. -/
def coverHom {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left) (i : ι) :
    coverOver family i ⟶ T :=
  Over.homMk (family i).hom rfl

/-- `coverHom family i` is the over-morphism induced by `(family i).hom`. -/
theorem coverOver_hom {S : Scheme.{u}} {T : Over S} {ι : Type u}
    (family : ι → Over T.left) (i : ι) :
    coverHom family i = Over.homMk (family i).hom rfl :=
  rfl

/-- The fibre product `T_i ×_T T_j`, viewed as a scheme over `S`. -/
def pairOver {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left) (i j : ι) :
    Over S :=
  Over.mk (pullback.fst (family i).hom (family j).hom ≫ (family i).hom ≫ T.hom)

/-- The projection `pr₀ : T_i ×_T T_j ⟶ T_i`. -/
def pr0 {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left) (i j : ι) :
    pairOver family i j ⟶ coverOver family i :=
  Over.homMk (pullback.fst (family i).hom (family j).hom) rfl

/-- Compatibility of `pr1` with the structure morphisms to `S`. -/
theorem pr1_w {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left) (i j : ι) :
    pullback.snd (family i).hom (family j).hom ≫ (coverOver family j).hom =
      (pairOver family i j).hom :=
  sorry

/-- The projection `pr₁ : T_i ×_T T_j ⟶ T_j`. -/
def pr1 {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left) (i j : ι) :
    pairOver family i j ⟶ coverOver family j :=
  Over.homMk (pullback.snd (family i).hom (family j).hom) (pr1_w family i j)

/-- `pr0` is induced by `pullback.fst`. -/
theorem pairOver_pr0 {S : Scheme.{u}} {T : Over S} {ι : Type u}
    (family : ι → Over T.left) (i j : ι) :
    pr0 family i j = Over.homMk (pullback.fst (family i).hom (family j).hom) rfl :=
  rfl

/-- `pr1` is induced by `pullback.snd`. -/
theorem pairOver_pr1 {S : Scheme.{u}} {T : Over S} {ι : Type u}
    (family : ι → Over T.left) (i j : ι) :
    pr1 family i j =
      Over.homMk (pullback.snd (family i).hom (family j).hom) (pr1_w family i j) :=
  rfl

/-- The two projections of `T_i ×_T T_j` agree after composing to `T`. -/
theorem pr0_coverHom {S : Scheme.{u}} {T : Over S} {ι : Type u}
    (family : ι → Over T.left) (i j : ι) :
    pr0 family i j ≫ coverHom family i = pr1 family i j ≫ coverHom family j :=
  sorry

/-- The triple fibre product `T_i ×_T T_j ×_T T_k`, as `(T_i ×_T T_j) ×_T T_k` over `S`. -/
def tripleOver {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (i j k : ι) : Over S :=
  Over.mk
    (pullback.fst (pullback.fst (family i).hom (family j).hom ≫ (family i).hom)
        (family k).hom ≫
      (pairOver family i j).hom)

/-- The projection `pr₀₁ : T_i ×_T T_j ×_T T_k ⟶ T_i ×_T T_j`. -/
def pr01 {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left) (i j k : ι) :
    tripleOver family i j k ⟶ pairOver family i j :=
  Over.homMk
    (pullback.fst (pullback.fst (family i).hom (family j).hom ≫ (family i).hom)
      (family k).hom)
    rfl

/-- The two legs of `pr12Scheme` agree over `T`. -/
theorem pr12Scheme_w {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (i j k : ι) :
    (pullback.fst (pullback.fst (family i).hom (family j).hom ≫ (family i).hom)
          (family k).hom ≫
        pullback.snd (family i).hom (family j).hom) ≫
        (family j).hom =
      pullback.snd (pullback.fst (family i).hom (family j).hom ≫ (family i).hom)
          (family k).hom ≫
        (family k).hom :=
  sorry

/-- Underlying scheme map of `pr₁₂`. -/
def pr12Scheme {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (i j k : ι) : (tripleOver family i j k).left ⟶ (pairOver family j k).left :=
  pullback.lift
    (pullback.fst (pullback.fst (family i).hom (family j).hom ≫ (family i).hom)
        (family k).hom ≫
      pullback.snd (family i).hom (family j).hom)
    (pullback.snd (pullback.fst (family i).hom (family j).hom ≫ (family i).hom)
      (family k).hom)
    (pr12Scheme_w family i j k)

/-- `pr12Scheme` lies over `S`. -/
theorem pr12_w {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (i j k : ι) :
    pr12Scheme family i j k ≫ (pairOver family j k).hom = (tripleOver family i j k).hom :=
  sorry

/-- The projection `pr₁₂ : T_i ×_T T_j ×_T T_k ⟶ T_j ×_T T_k`. -/
def pr12 {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left) (i j k : ι) :
    tripleOver family i j k ⟶ pairOver family j k :=
  Over.homMk (pr12Scheme family i j k) (pr12_w family i j k)

/-- The two legs of `pr02Scheme` agree over `T`. -/
theorem pr02Scheme_w {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (i j k : ι) :
    (pullback.fst (pullback.fst (family i).hom (family j).hom ≫ (family i).hom)
          (family k).hom ≫
        pullback.fst (family i).hom (family j).hom) ≫
        (family i).hom =
      pullback.snd (pullback.fst (family i).hom (family j).hom ≫ (family i).hom)
          (family k).hom ≫
        (family k).hom :=
  sorry

/-- Underlying scheme map of `pr₀₂`. -/
def pr02Scheme {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (i j k : ι) : (tripleOver family i j k).left ⟶ (pairOver family i k).left :=
  pullback.lift
    (pullback.fst (pullback.fst (family i).hom (family j).hom ≫ (family i).hom)
        (family k).hom ≫
      pullback.fst (family i).hom (family j).hom)
    (pullback.snd (pullback.fst (family i).hom (family j).hom ≫ (family i).hom)
      (family k).hom)
    (pr02Scheme_w family i j k)

/-- `pr02Scheme` lies over `S`. -/
theorem pr02_w {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (i j k : ι) :
    pr02Scheme family i j k ≫ (pairOver family i k).hom = (tripleOver family i j k).hom :=
  sorry

/-- The projection `pr₀₂ : T_i ×_T T_j ×_T T_k ⟶ T_i ×_T T_k`. -/
def pr02 {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left) (i j k : ι) :
    tripleOver family i j k ⟶ pairOver family i k :=
  Over.homMk (pr02Scheme family i j k) (pr02_w family i j k)


namespace DescentDatum

/-- The identity covering `{T ⟶ T}` as a `PUnit`-indexed family. -/
def identityFamily {S : Scheme.{u}} (T : Over S) : PUnit.{u + 1} → Over T.left :=
  fun _ ↦ Over.mk (𝟙 T.left)

/-- The identity covering member is `T` over `S`. -/
def identityCoverHom {S : Scheme.{u}} (T : Over S) :
    coverOver (identityFamily T) PUnit.unit ⟶ T :=
  Over.homMk (𝟙 T.left) rfl

/-- The pair of the identity covering maps to `T` by `pr₀`. -/
def identityPairHom {S : Scheme.{u}} (T : Over S) :
    pairOver (identityFamily T) PUnit.unit PUnit.unit ⟶ T :=
  Over.homMk (pullback.fst (𝟙 T.left) (𝟙 T.left) ≫ 𝟙 T.left) rfl


/-- Compatibility of a covering member of a refinement with the structure maps to `S`. -/
theorem coverMap_w {S : Scheme.{u}} {T : Over S} {ι ι' : Type u}
    {family : ι → Over T.left} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) (j : ι') :
    (φ j).left ≫ (coverOver family (α j)).hom = (coverOver family' j).hom :=
  sorry

/-- The morphism `T'_j ⟶ T_{α(j)}` of a refinement, as a map of schemes over `S`. -/
def coverMap {S : Scheme.{u}} {T : Over S} {ι ι' : Type u}
    {family : ι → Over T.left} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) (j : ι') :
    coverOver family' j ⟶ coverOver family (α j) :=
  Over.homMk (φ j).left (coverMap_w α φ j)

/-- A refinement map commutes with the structure morphisms to `T`. -/
theorem coverMap_coverHom {S : Scheme.{u}} {T : Over S} {ι ι' : Type u}
    {family : ι → Over T.left} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) (j : ι') :
    coverMap α φ j ≫ coverHom family (α j) = coverHom family' j :=
  sorry

/-- Underlying scheme map of a pairwise refinement. -/
def pairMapScheme {S : Scheme.{u}} {T : Over S} {ι ι' : Type u}
    {family : ι → Over T.left} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) (j j' : ι') :
    (pairOver family' j j').left ⟶ (pairOver family (α j) (α j')).left :=
  pullback.map (family' j).hom (family' j').hom (family (α j)).hom (family (α j')).hom
    (φ j).left (φ j').left (𝟙 T.left)
    ((Category.comp_id (family' j).hom).trans (Over.w (φ j)).symm)
    ((Category.comp_id (family' j').hom).trans (Over.w (φ j')).symm)

/-- `pairMapScheme` lies over `S`. -/
theorem pairMap_w {S : Scheme.{u}} {T : Over S} {ι ι' : Type u}
    {family : ι → Over T.left} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) (j j' : ι') :
    pairMapScheme α φ j j' ≫ (pairOver family (α j) (α j')).hom =
      (pairOver family' j j').hom :=
  sorry

/-- The morphism `T'_j ×_T T'_{j'} ⟶ T_{α(j)} ×_T T_{α(j')}` of a refinement. -/
def pairMap {S : Scheme.{u}} {T : Over S} {ι ι' : Type u}
    {family : ι → Over T.left} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) (j j' : ι') :
    pairOver family' j j' ⟶ pairOver family (α j) (α j') :=
  Over.homMk (pairMapScheme α φ j j') (pairMap_w α φ j j')


end DescentDatum

end AlgebraicGeometry.GroupoidAlgebraicSpace
