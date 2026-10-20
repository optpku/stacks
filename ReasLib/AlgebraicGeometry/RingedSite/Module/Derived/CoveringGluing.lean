module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Over
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Derived.Restriction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization

/-!
# Covering-indexed derived glueing data

A covering family of derived modules on a ringed site records objects `E_i` on the
members of `{U_i ⟶ X}` together with cocycle isomorphisms `ρ_ij` on the fibre
products `U_i ×_X U_j`. A solution is a global object of
`ModuleDerived (C.localization X)` with compatible identifications on each `U_i`.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits
open RingedSite RingedSite.Hom
open SheafOfModules.Derived

noncomputable section

universe ι u v w

namespace RingedSite.ModuleDerived

variable {C : RingedSite.{u, v, w}} {X : C}
variable [HasPullbacks C.carrier] [UnivLE.{max u v, w}]

/-- The fibre product `U_i ×_X U_j` of two members of a covering family. -/
def CoveringFamily.overlap (𝒰 : FormalCoproduct.{ι} (Over X)) (i j : 𝒰.I) : C :=
  pullback (𝒰.obj i).hom (𝒰.obj j).hom

/-- The first projection `U_i ×_X U_j ⟶ U_i`. -/
def CoveringFamily.overlapπ₁ (𝒰 : FormalCoproduct.{ι} (Over X)) (i j : 𝒰.I) :
    CoveringFamily.overlap 𝒰 i j ⟶ (𝒰.obj i).left :=
  pullback.fst (𝒰.obj i).hom (𝒰.obj j).hom

/-- The second projection `U_i ×_X U_j ⟶ U_j`. -/
def CoveringFamily.overlapπ₂ (𝒰 : FormalCoproduct.{ι} (Over X)) (i j : 𝒰.I) :
    CoveringFamily.overlap 𝒰 i j ⟶ (𝒰.obj j).left :=
  pullback.snd (𝒰.obj i).hom (𝒰.obj j).hom

/-- The overlap object is the chosen fibre product of the structure maps. -/
theorem CoveringFamily.overlap_eq (𝒰 : FormalCoproduct.{ι} (Over X)) (i j : 𝒰.I) :
    CoveringFamily.overlap 𝒰 i j = pullback (𝒰.obj i).hom (𝒰.obj j).hom :=
  sorry

/-- The first overlap projection is `pullback.fst`. -/
theorem CoveringFamily.overlapπ₁_eq (𝒰 : FormalCoproduct.{ι} (Over X)) (i j : 𝒰.I) :
    CoveringFamily.overlapπ₁ 𝒰 i j = pullback.fst (𝒰.obj i).hom (𝒰.obj j).hom :=
  sorry

/-- The second overlap projection is `pullback.snd`. -/
theorem CoveringFamily.overlapπ₂_eq (𝒰 : FormalCoproduct.{ι} (Over X)) (i j : 𝒰.I) :
    CoveringFamily.overlapπ₂ 𝒰 i j = pullback.snd (𝒰.obj i).hom (𝒰.obj j).hom :=
  sorry

/-- The two projections `U_i ×_X U_j ⟶ X` agree. -/
theorem CoveringFamily.overlap_condition (𝒰 : FormalCoproduct.{ι} (Over X))
    (i j : 𝒰.I) :
    CoveringFamily.overlapπ₁ 𝒰 i j ≫ (𝒰.obj i).hom =
      CoveringFamily.overlapπ₂ 𝒰 i j ≫ (𝒰.obj j).hom :=
  sorry

/-- The triple fibre product `U_i ×_X U_j ×_X U_k`. -/
def CoveringFamily.triple (𝒰 : FormalCoproduct.{ι} (Over X)) (i j k : 𝒰.I) : C :=
  pullback (CoveringFamily.overlapπ₁ 𝒰 i j ≫ (𝒰.obj i).hom) (𝒰.obj k).hom

/-- The projection `U_ijk ⟶ U_ij`. -/
def CoveringFamily.tripleπ₁₂ (𝒰 : FormalCoproduct.{ι} (Over X)) (i j k : 𝒰.I) :
    CoveringFamily.triple 𝒰 i j k ⟶ CoveringFamily.overlap 𝒰 i j :=
  pullback.fst (CoveringFamily.overlapπ₁ 𝒰 i j ≫ (𝒰.obj i).hom) (𝒰.obj k).hom

/-- The projection `U_ijk ⟶ U_ik`. -/
def CoveringFamily.tripleπ₁₃ (𝒰 : FormalCoproduct.{ι} (Over X)) (i j k : 𝒰.I) :
    CoveringFamily.triple 𝒰 i j k ⟶ CoveringFamily.overlap 𝒰 i k :=
  pullback.lift
    (CoveringFamily.tripleπ₁₂ 𝒰 i j k ≫ CoveringFamily.overlapπ₁ 𝒰 i j)
    (pullback.snd (CoveringFamily.overlapπ₁ 𝒰 i j ≫ (𝒰.obj i).hom) (𝒰.obj k).hom)
    ((Category.assoc (CoveringFamily.tripleπ₁₂ 𝒰 i j k)
        (CoveringFamily.overlapπ₁ 𝒰 i j) (𝒰.obj i).hom).trans pullback.condition)

/-- The projection `U_ijk ⟶ U_jk`. -/
def CoveringFamily.tripleπ₂₃ (𝒰 : FormalCoproduct.{ι} (Over X)) (i j k : 𝒰.I) :
    CoveringFamily.triple 𝒰 i j k ⟶ CoveringFamily.overlap 𝒰 j k :=
  pullback.lift
    (CoveringFamily.tripleπ₁₂ 𝒰 i j k ≫ CoveringFamily.overlapπ₂ 𝒰 i j)
    (pullback.snd (CoveringFamily.overlapπ₁ 𝒰 i j ≫ (𝒰.obj i).hom) (𝒰.obj k).hom)
    ((Category.assoc (CoveringFamily.tripleπ₁₂ 𝒰 i j k)
        (CoveringFamily.overlapπ₂ 𝒰 i j) (𝒰.obj j).hom).trans
      ((congrArg (CategoryStruct.comp (CoveringFamily.tripleπ₁₂ 𝒰 i j k))
          pullback.condition.symm).trans pullback.condition))

/-- The triple object is the chosen fibre product of `U_ij ⟶ X` with `U_k ⟶ X`. -/
theorem CoveringFamily.triple_eq (𝒰 : FormalCoproduct.{ι} (Over X))
    (i j k : 𝒰.I) :
    CoveringFamily.triple 𝒰 i j k =
      pullback (CoveringFamily.overlapπ₁ 𝒰 i j ≫ (𝒰.obj i).hom) (𝒰.obj k).hom :=
  sorry

/-- The two projections `U_ijk ⟶ U_i` agree. -/
theorem CoveringFamily.tripleπ₁₂_comp_overlapπ₁ (𝒰 : FormalCoproduct.{ι} (Over X))
    (i j k : 𝒰.I) :
    CoveringFamily.tripleπ₁₂ 𝒰 i j k ≫ CoveringFamily.overlapπ₁ 𝒰 i j =
      CoveringFamily.tripleπ₁₃ 𝒰 i j k ≫ CoveringFamily.overlapπ₁ 𝒰 i k :=
  sorry

/-- The two projections `U_ijk ⟶ U_j` agree. -/
theorem CoveringFamily.tripleπ₁₂_comp_overlapπ₂ (𝒰 : FormalCoproduct.{ι} (Over X))
    (i j k : 𝒰.I) :
    CoveringFamily.tripleπ₁₂ 𝒰 i j k ≫ CoveringFamily.overlapπ₂ 𝒰 i j =
      CoveringFamily.tripleπ₂₃ 𝒰 i j k ≫ CoveringFamily.overlapπ₁ 𝒰 j k :=
  sorry

/-- The two projections `U_ijk ⟶ U_k` agree. -/
theorem CoveringFamily.tripleπ₁₃_comp_overlapπ₂ (𝒰 : FormalCoproduct.{ι} (Over X))
    (i j k : 𝒰.I) :
    CoveringFamily.tripleπ₁₃ 𝒰 i j k ≫ CoveringFamily.overlapπ₂ 𝒰 i k =
      CoveringFamily.tripleπ₂₃ 𝒰 i j k ≫ CoveringFamily.overlapπ₂ 𝒰 j k :=
  sorry

/-- A covering-indexed derived glueing datum: objects `E_i` of
`ModuleDerived (C.localization U_i)` and cocycle isomorphisms
`ρ_ij : E_i|_{U_ij} ≅ E_j|_{U_ij}` on `U_i ×_X U_j`. -/
structure CoveringFamily (C : RingedSite.{u, v, w}) (X : C)
    [HasPullbacks C.carrier] [UnivLE.{max u v, w}]
    (𝒰 : FormalCoproduct.{ι} (Over X)) where
  /-- The object `E_i` of `ModuleDerived (C.localization U_i)`. -/
  obj (i : 𝒰.I) : ModuleDerived.{w} (C.localization (𝒰.obj i).left)
  /-- The isomorphism `ρ_ij : E_i|_{U_ij} ≅ E_j|_{U_ij}`. -/
  iso (i j : 𝒰.I) :
    (restrictionDerived C.structureSheaf
        (abelianOver := fun U => localizedModuleCatAbelian U) (CoveringFamily.overlapπ₁ 𝒰 i j)).obj (obj i) ≅
      (restrictionDerived C.structureSheaf
          (abelianOver := fun U => localizedModuleCatAbelian U) (CoveringFamily.overlapπ₂ 𝒰 i j)).obj (obj j)
  /-- The Čech cocycle condition for `ρ_ij` on `U_i ×_X U_j ×_X U_k`. -/
  iso_comp (i j k : 𝒰.I) :
    (restrictionDerived C.structureSheaf
        (abelianOver := fun U => localizedModuleCatAbelian U) (CoveringFamily.tripleπ₁₃ 𝒰 i j k)).mapIso
          (iso i k) =
      (((restrictionCompIso C.structureSheaf
          (abelianOver := fun U => localizedModuleCatAbelian U) (CoveringFamily.overlapπ₁ 𝒰 i k)
            (CoveringFamily.tripleπ₁₃ 𝒰 i j k)).app (obj i))).symm ≪≫
        (restrictionDerivedCongr C.structureSheaf
            (abelianOver := fun U => localizedModuleCatAbelian U)
            (CoveringFamily.tripleπ₁₂_comp_overlapπ₁ 𝒰 i j k).symm).app (obj i) ≪≫
        ((restrictionCompIso C.structureSheaf
            (abelianOver := fun U => localizedModuleCatAbelian U) (CoveringFamily.overlapπ₁ 𝒰 i j)
              (CoveringFamily.tripleπ₁₂ 𝒰 i j k)).app (obj i)) ≪≫
        (restrictionDerived C.structureSheaf
            (abelianOver := fun U => localizedModuleCatAbelian U) (CoveringFamily.tripleπ₁₂ 𝒰 i j k)).mapIso
              (iso i j) ≪≫
        (((restrictionCompIso C.structureSheaf
            (abelianOver := fun U => localizedModuleCatAbelian U) (CoveringFamily.overlapπ₂ 𝒰 i j)
              (CoveringFamily.tripleπ₁₂ 𝒰 i j k)).app (obj j))).symm ≪≫
        (restrictionDerivedCongr C.structureSheaf
            (abelianOver := fun U => localizedModuleCatAbelian U)
            (CoveringFamily.tripleπ₁₂_comp_overlapπ₂ 𝒰 i j k)).app (obj j) ≪≫
        ((restrictionCompIso C.structureSheaf
            (abelianOver := fun U => localizedModuleCatAbelian U) (CoveringFamily.overlapπ₁ 𝒰 j k)
              (CoveringFamily.tripleπ₂₃ 𝒰 i j k)).app (obj j)) ≪≫
        (restrictionDerived C.structureSheaf
            (abelianOver := fun U => localizedModuleCatAbelian U) (CoveringFamily.tripleπ₂₃ 𝒰 i j k)).mapIso
              (iso j k) ≪≫
        (((restrictionCompIso C.structureSheaf
            (abelianOver := fun U => localizedModuleCatAbelian U) (CoveringFamily.overlapπ₂ 𝒰 j k)
              (CoveringFamily.tripleπ₂₃ 𝒰 i j k)).app (obj k))).symm ≪≫
        (restrictionDerivedCongr C.structureSheaf
            (abelianOver := fun U => localizedModuleCatAbelian U)
            (CoveringFamily.tripleπ₁₃_comp_overlapπ₂ 𝒰 i j k).symm).app (obj k) ≪≫
        ((restrictionCompIso C.structureSheaf
            (abelianOver := fun U => localizedModuleCatAbelian U) (CoveringFamily.overlapπ₂ 𝒰 i k)
              (CoveringFamily.tripleπ₁₃ 𝒰 i j k)).app (obj k))

namespace CoveringFamily

variable {𝒰 : FormalCoproduct.{ι} (Over X)}

/-- The Čech cocycle of a covering glueing datum. -/
theorem spec (G : CoveringFamily C X 𝒰) (i j k : 𝒰.I) :
    (restrictionDerived C.structureSheaf
        (abelianOver := fun U => localizedModuleCatAbelian U) (tripleπ₁₃ 𝒰 i j k)).mapIso (G.iso i k) =
      (((restrictionCompIso C.structureSheaf
          (abelianOver := fun U => localizedModuleCatAbelian U) (overlapπ₁ 𝒰 i k) (tripleπ₁₃ 𝒰 i j k)).app
            (G.obj i))).symm ≪≫
        (restrictionDerivedCongr C.structureSheaf
            (abelianOver := fun U => localizedModuleCatAbelian U) (tripleπ₁₂_comp_overlapπ₁ 𝒰 i j k).symm).app
          (G.obj i) ≪≫
        ((restrictionCompIso C.structureSheaf
            (abelianOver := fun U => localizedModuleCatAbelian U) (overlapπ₁ 𝒰 i j) (tripleπ₁₂ 𝒰 i j k)).app
              (G.obj i)) ≪≫
        (restrictionDerived C.structureSheaf
            (abelianOver := fun U => localizedModuleCatAbelian U) (tripleπ₁₂ 𝒰 i j k)).mapIso (G.iso i j) ≪≫
        (((restrictionCompIso C.structureSheaf
            (abelianOver := fun U => localizedModuleCatAbelian U) (overlapπ₂ 𝒰 i j) (tripleπ₁₂ 𝒰 i j k)).app
              (G.obj j))).symm ≪≫
        (restrictionDerivedCongr C.structureSheaf
            (abelianOver := fun U => localizedModuleCatAbelian U) (tripleπ₁₂_comp_overlapπ₂ 𝒰 i j k)).app
          (G.obj j) ≪≫
        ((restrictionCompIso C.structureSheaf
            (abelianOver := fun U => localizedModuleCatAbelian U) (overlapπ₁ 𝒰 j k) (tripleπ₂₃ 𝒰 i j k)).app
              (G.obj j)) ≪≫
        (restrictionDerived C.structureSheaf
            (abelianOver := fun U => localizedModuleCatAbelian U) (tripleπ₂₃ 𝒰 i j k)).mapIso (G.iso j k) ≪≫
        (((restrictionCompIso C.structureSheaf
            (abelianOver := fun U => localizedModuleCatAbelian U) (overlapπ₂ 𝒰 j k) (tripleπ₂₃ 𝒰 i j k)).app
              (G.obj k))).symm ≪≫
        (restrictionDerivedCongr C.structureSheaf
            (abelianOver := fun U => localizedModuleCatAbelian U) (tripleπ₁₃_comp_overlapπ₂ 𝒰 i j k).symm).app
          (G.obj k) ≪≫
        ((restrictionCompIso C.structureSheaf
            (abelianOver := fun U => localizedModuleCatAbelian U) (overlapπ₂ 𝒰 i k) (tripleπ₁₃ 𝒰 i j k)).app
              (G.obj k)) :=
  sorry

/-- The tautological covering glueing datum attached to a global object `E` of
`ModuleDerived (C.localization X)`. -/
def ofGlobal (𝒰 : FormalCoproduct.{ι} (Over X))
    (E : ModuleDerived.{w} (C.localization X)) :
    CoveringFamily C X 𝒰 where
  obj i := (restrictionDerived C.structureSheaf
      (abelianOver := fun U => localizedModuleCatAbelian U) (𝒰.obj i).hom).obj E
  iso i j :=
    (restrictionCompIso C.structureSheaf
        (abelianOver := fun U => localizedModuleCatAbelian U) (𝒰.obj i).hom (overlapπ₁ 𝒰 i j)).symm.app E ≪≫
      (restrictionDerivedCongr C.structureSheaf
          (abelianOver := fun U => localizedModuleCatAbelian U) pullback.condition).app E ≪≫
      (restrictionCompIso C.structureSheaf
          (abelianOver := fun U => localizedModuleCatAbelian U) (𝒰.obj j).hom (overlapπ₂ 𝒰 i j)).app E
  iso_comp := sorry

/-- The local object of `ofGlobal E` is the restriction of `E` along `U_i ⟶ X`. -/
theorem ofGlobal_obj (𝒰 : FormalCoproduct.{ι} (Over X))
    (E : ModuleDerived.{w} (C.localization X)) (i : 𝒰.I) :
    (ofGlobal 𝒰 E).obj i = (restrictionDerived C.structureSheaf
        (abelianOver := fun U => localizedModuleCatAbelian U) (𝒰.obj i).hom).obj E :=
  sorry

/-- The overlap isomorphism of `ofGlobal E` is the canonical restriction comparison. -/
theorem ofGlobal_iso (𝒰 : FormalCoproduct.{ι} (Over X))
    (E : ModuleDerived.{w} (C.localization X)) (i j : 𝒰.I) :
    (ofGlobal 𝒰 E).iso i j =
      (restrictionCompIso C.structureSheaf
          (abelianOver := fun U => localizedModuleCatAbelian U) (𝒰.obj i).hom (overlapπ₁ 𝒰 i j)).symm.app E ≪≫
        (restrictionDerivedCongr C.structureSheaf
            (abelianOver := fun U => localizedModuleCatAbelian U) pullback.condition).app E ≪≫
        (restrictionCompIso C.structureSheaf
            (abelianOver := fun U => localizedModuleCatAbelian U) (𝒰.obj j).hom (overlapπ₂ 𝒰 i j)).app E :=
  sorry

/-- Negative self-Ext sheaves of each `E_i` vanish: for every arrow `V ⟶ U_i` and
every `t > 0`, the Hom-space `Hom((E_i|_V)⟦t⟧, E_i|_V)` is a subsingleton. -/
def negativeSheafSelfExt (G : CoveringFamily C X 𝒰) : Prop :=
  ∀ (i : 𝒰.I) {V : C} (f : V ⟶ (𝒰.obj i).left) (t : ℤ),
    0 < t →
      Subsingleton
        (((restrictionDerived C.structureSheaf
            (abelianOver := fun U => localizedModuleCatAbelian U) f).obj (G.obj i))⟦t⟧ ⟶
          (restrictionDerived C.structureSheaf
              (abelianOver := fun U => localizedModuleCatAbelian U) f).obj (G.obj i))

/-- Unfolding of sheaf-level negative self-Ext vanishing. -/
theorem negativeSheafSelfExt_iff (G : CoveringFamily C X 𝒰) :
    G.negativeSheafSelfExt ↔
      ∀ (i : 𝒰.I) {V : C} (f : V ⟶ (𝒰.obj i).left) (t : ℤ),
        0 < t →
          Subsingleton
            (((restrictionDerived C.structureSheaf
                (abelianOver := fun U => localizedModuleCatAbelian U) f).obj (G.obj i))⟦t⟧ ⟶
              (restrictionDerived C.structureSheaf
                  (abelianOver := fun U => localizedModuleCatAbelian U) f).obj (G.obj i)) :=
  sorry

/-- The objects `E_i` are uniformly bounded below: a single integer `t` kills
homology of every `E_i` in degrees `< t`. -/
def uniformlyBoundedBelow (G : CoveringFamily C X 𝒰) : Prop :=
  ∃ t : ℤ, ∀ (i : 𝒰.I) (p : ℤ), p < t →
    IsZero ((DerivedCategory.homologyFunctor _ p).obj (G.obj i))

/-- Unfolding of uniform boundedness below. -/
theorem uniformlyBoundedBelow_iff (G : CoveringFamily C X 𝒰) :
    G.uniformlyBoundedBelow ↔
      ∃ t : ℤ, ∀ (i : 𝒰.I) (p : ℤ), p < t →
        IsZero ((DerivedCategory.homologyFunctor _ p).obj (G.obj i)) :=
  sorry

/-- A solution of a covering glueing datum is a global object `E` of
`ModuleDerived (C.localization X)` with isomorphisms `ρ_i : E|_{U_i} ≅ E_i`
compatible with the given `ρ_ij`. -/
structure Solution (G : CoveringFamily C X 𝒰) where
  /-- The global object `E` of `ModuleDerived (C.localization X)`. -/
  obj : ModuleDerived.{w} (C.localization X)
  /-- The isomorphism `ρ_i : E|_{U_i} ≅ E_i`. -/
  iso (i : 𝒰.I) :
    (restrictionDerived C.structureSheaf
        (abelianOver := fun U => localizedModuleCatAbelian U) (𝒰.obj i).hom).obj obj ≅ G.obj i
  /-- Compatibility of `ρ_i` and `ρ_j` with `ρ_ij` after restriction to `U_ij`. -/
  iso_comp (i j : 𝒰.I) :
    (restrictionDerived C.structureSheaf
        (abelianOver := fun U => localizedModuleCatAbelian U) (overlapπ₁ 𝒰 i j)).mapIso (iso i) ≪≫ G.iso i j =
      (restrictionCompIso C.structureSheaf
          (abelianOver := fun U => localizedModuleCatAbelian U) (𝒰.obj i).hom (overlapπ₁ 𝒰 i j)).symm.app obj
            ≪≫
        (restrictionDerivedCongr C.structureSheaf
            (abelianOver := fun U => localizedModuleCatAbelian U) pullback.condition).app obj ≪≫
        (restrictionCompIso C.structureSheaf
            (abelianOver := fun U => localizedModuleCatAbelian U) (𝒰.obj j).hom (overlapπ₂ 𝒰 i j)).app obj ≪≫
        (restrictionDerived C.structureSheaf
            (abelianOver := fun U => localizedModuleCatAbelian U) (overlapπ₂ 𝒰 i j)).mapIso (iso j)

namespace Solution

/-- An isomorphism of global objects is compatible with two solutions when its
restrictions intertwine the identifications `ρ_i`. -/
abbrev IsCompatibleIso {G : CoveringFamily C X 𝒰}
    (S S' : Solution G) (e : S.obj ≅ S'.obj) : Prop :=
  ∀ i : 𝒰.I,
    (restrictionDerived C.structureSheaf
        (abelianOver := fun U => localizedModuleCatAbelian U) (𝒰.obj i).hom).map e.hom ≫ (S'.iso i).hom =
      (S.iso i).hom

/-- Equational form of compatibility of an isomorphism between solutions. -/
theorem IsCompatibleIso.w {G : CoveringFamily C X 𝒰} {S S' : Solution G}
    {e : S.obj ≅ S'.obj} (h : IsCompatibleIso S S' e) (i : 𝒰.I) :
    (restrictionDerived C.structureSheaf
        (abelianOver := fun U => localizedModuleCatAbelian U) (𝒰.obj i).hom).map e.hom ≫ (S'.iso i).hom =
      (S.iso i).hom :=
  sorry

/-- The tautological solution of `ofGlobal E`. -/
def ofGlobal (𝒰 : FormalCoproduct.{ι} (Over X))
    (E : ModuleDerived.{w} (C.localization X)) :
    Solution (CoveringFamily.ofGlobal 𝒰 E) where
  obj := E
  iso i := Iso.refl _
  iso_comp := sorry

/-- The global object of the tautological solution is the original object. -/
theorem ofGlobal_obj (𝒰 : FormalCoproduct.{ι} (Over X))
    (E : ModuleDerived.{w} (C.localization X)) :
    (ofGlobal 𝒰 E).obj = E :=
  sorry

end Solution

variable (G : CoveringFamily C X 𝒰)

/-- Let `(C, O_C)` be a ringed site with fibre products, and let `{U_i ⟶ X}` be a
covering. Given objects `E_i` of `ModuleDerived (C.localization U_i)` and
cocycle isomorphisms `ρ_ij : E_i|_{U_ij} ≅ E_j|_{U_ij}` on
`U_ij = U_i ×_X U_j`, if the negative self-Ext sheaves of each `E_i` vanish and
the `E_i` are uniformly bounded below, then a solution exists. -/
@[stacks 0GMG]
theorem exists_solution (h_cover : 𝒰.toSieve ∈ C.siteTopology X)
    (h_neg : G.negativeSheafSelfExt) (h_bound : G.uniformlyBoundedBelow) :
    Nonempty (Solution G) :=
  sorry

/-- For a covering glueing datum with vanishing negative self-Ext sheaves and
a uniform lower cohomological bound, any two solutions have a unique
isomorphism of global objects compatible with their local identifications. -/
@[stacks 0GMG]
theorem unique_hom_solution (h_cover : 𝒰.toSieve ∈ C.siteTopology X)
    (h_neg : G.negativeSheafSelfExt) (h_bound : G.uniformlyBoundedBelow)
    (S S' : Solution G) :
    ∃ e : S.obj ≅ S'.obj,
      Solution.IsCompatibleIso S S' e ∧
        ∀ e' : S.obj ≅ S'.obj, Solution.IsCompatibleIso S S' e' →
          e'.hom = e.hom :=
  sorry

end CoveringFamily

end RingedSite.ModuleDerived
