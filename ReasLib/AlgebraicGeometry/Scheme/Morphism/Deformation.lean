/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.Deformation

variable {S X X' Y Y' : Scheme.{u}}

/-- The conormal map induced by a commutative square from the restriction of
`a^* C_{Y/Y'}` to `i ⁻¹ᵁ U'`. -/
noncomputable def inducedConormalMap (i : X ⟶ X') (j : Y ⟶ Y') (a : X ⟶ Y)
    (U' : X'.Opens) (a' : U'.toScheme ⟶ Y')
    (sq : CommSq ((i ⁻¹ᵁ U').ι ≫ a) (i ∣_ U') j a') :
    (Scheme.Modules.restrictFunctor (i ⁻¹ᵁ U').ι).obj
        ((Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j)) ⟶
      Scheme.Hom.conormalSheaf (i ∣_ U') :=
  (Scheme.Modules.restrictFunctorIsoPullback (i ⁻¹ᵁ U').ι).hom.app _ ≫
    (Scheme.Modules.pullbackComp (i ⁻¹ᵁ U').ι a).hom.app _ ≫
      Scheme.Hom.Conormal.map sq

/-- The explicit composite defining `inducedConormalMap`. -/
theorem inducedConormalMap_def (i : X ⟶ X') (j : Y ⟶ Y') (a : X ⟶ Y)
    (U' : X'.Opens) (a' : U'.toScheme ⟶ Y')
    (sq : CommSq ((i ⁻¹ᵁ U').ι ≫ a) (i ∣_ U') j a') :
    inducedConormalMap i j a U' a' sq =
      (Scheme.Modules.restrictFunctorIsoPullback (i ⁻¹ᵁ U').ι).hom.app _ ≫
        (Scheme.Modules.pullbackComp (i ⁻¹ᵁ U').ι a).hom.app _ ≫
          Scheme.Hom.Conormal.map sq := rfl

/-- The restriction of a fixed conormal map to `i ⁻¹ᵁ U'`, transported to the
conormal sheaf of `i ∣_ U'`. -/
noncomputable def restrictedConormalMap (i : X ⟶ X') (j : Y ⟶ Y') (a : X ⟶ Y)
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i)
    (U' : X'.Opens) :
    (Scheme.Modules.restrictFunctor (i ⁻¹ᵁ U').ι).obj
        ((Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j)) ⟶
      Scheme.Hom.conormalSheaf (i ∣_ U') :=
  (Scheme.Modules.restrictFunctor (i ⁻¹ᵁ U').ι).map A ≫
    (Scheme.Modules.restrictFunctorIsoPullback (i ⁻¹ᵁ U').ι).hom.app _ ≫
      Scheme.Hom.Conormal.map ((isPullback_morphismRestrict i U').flip.toCommSq)

/-- The explicit composite defining `restrictedConormalMap`. -/
theorem restrictedConormalMap_def (i : X ⟶ X') (j : Y ⟶ Y') (a : X ⟶ Y)
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i)
    (U' : X'.Opens) :
    restrictedConormalMap i j a A U' =
      (Scheme.Modules.restrictFunctor (i ⁻¹ᵁ U').ι).map A ≫
        (Scheme.Modules.restrictFunctorIsoPullback (i ⁻¹ᵁ U').ι).hom.app _ ≫
          Scheme.Hom.Conormal.map
            ((isPullback_morphismRestrict i U').flip.toCommSq) := rfl

/-- A local lift is compatible with the base scheme, the given map on the
first-order closed subscheme, and the prescribed conormal map. -/
def IsCompatible (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y') (a : X ⟶ Y)
    [X'.Over S] [Y'.Over S]
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i)
    (U' : X'.Opens) (a' : U'.toScheme ⟶ Y') : Prop :=
  a' ≫ (Y' ↘ S) = U'.ι ≫ (X' ↘ S) ∧
    ∃ sq : CommSq ((i ⁻¹ᵁ U').ι ≫ a) (i ∣_ U') j a',
      inducedConormalMap i j a U' a' sq = restrictedConormalMap i j a A U'

/-- The three dependent compatibility conditions for a local lift. -/
theorem isCompatible_iff (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y') (a : X ⟶ Y)
    [X'.Over S] [Y'.Over S]
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i)
    (U' : X'.Opens) (a' : U'.toScheme ⟶ Y') :
    IsCompatible S i j a A U' a' ↔
      a' ≫ (Y' ↘ S) = U'.ι ≫ (X' ↘ S) ∧
        ∃ sq : CommSq ((i ⁻¹ᵁ U').ι ≫ a) (i ∣_ U') j a',
          inducedConormalMap i j a U' a' sq =
            restrictedConormalMap i j a A U' := Iff.rfl

/-- The set of compatible local deformations of `a` on an open subscheme of `X'`. -/
def sections (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y') (a : X ⟶ Y)
    [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i)
    (U' : X'.Opens) : Set (U'.toScheme ⟶ Y') :=
  {a' | IsCompatible S i j a A U' a'}

/-- Membership in `sections` is the local compatibility predicate. -/
theorem mem_sections_iff (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y') (a : X ⟶ Y)
    [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i)
    (U' : X'.Opens) (a' : U'.toScheme ⟶ Y') :
    a' ∈ sections S i j a A U' ↔ IsCompatible S i j a A U' a' := Iff.rfl

/-- Restrict a candidate local deformation along an inclusion of opens. -/
def restrictHom {U' V' : X'.Opens} (h : V' ≤ U') (a' : U'.toScheme ⟶ Y') :
    V'.toScheme ⟶ Y' :=
  X'.homOfLE h ≫ a'

/-- Restriction of a candidate along the identity inclusion is unchanged. -/
theorem restrictHom_id (U' : X'.Opens) (a' : U'.toScheme ⟶ Y') :
    restrictHom (le_refl U') a' = a' := by
  simp [restrictHom]

/-- Successive restrictions of a candidate agree with restriction along the composite inclusion. -/
theorem restrictHom_comp {U' V' W' : X'.Opens} (hWV : W' ≤ V') (hVU : V' ≤ U')
    (a' : U'.toScheme ⟶ Y') :
    restrictHom hWV (restrictHom hVU a') = restrictHom (hWV.trans hVU) a' := by
  dsimp only [restrictHom]
  rw [← Category.assoc, Scheme.homOfLE_homOfLE]

/-- Restricting a compatible local deformation gives a compatible local deformation. -/
theorem mem_sections_restrictHom (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
    (a : X ⟶ Y) [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i)
    {U' V' : X'.Opens} (h : V' ≤ U') (a' : U'.toScheme ⟶ Y')
    (ha' : a' ∈ sections S i j a A U') :
    restrictHom h a' ∈ sections S i j a A V' := by
  change IsCompatible S i j a A U' a' at ha'
  change IsCompatible S i j a A V' (restrictHom h a')
  rcases ha' with ⟨hbase, sq⟩
  rcases sq with ⟨sq, hsq⟩
  constructor
  · dsimp only [restrictHom]
    rw [Category.assoc, hbase, ← Category.assoc, Scheme.homOfLE_ι]
  · let sqV : CommSq ((i ⁻¹ᵁ V').ι ≫ a) (i ∣_ V') j (restrictHom h a') :=
      ⟨by
        dsimp only [restrictHom]
        rw [← Scheme.homOfLE_ι X (i.preimage_mono h)]
        calc
          X.homOfLE (i.preimage_mono h) ≫ (i ⁻¹ᵁ U').ι ≫ a ≫ j =
              X.homOfLE (i.preimage_mono h) ≫ ((i ⁻¹ᵁ U').ι ≫ a) ≫ j := by
                simp only [Category.assoc]
          _ = X.homOfLE (i.preimage_mono h) ≫ ((i ∣_ U') ≫ a') := by
            rw [sq.w]
          _ = (i ∣_ V') ≫ X'.homOfLE h ≫ a' := by
            calc
              X.homOfLE (i.preimage_mono h) ≫ (i ∣_ U') ≫ a' =
                  (X.homOfLE (i.preimage_mono h) ≫ (i ∣_ U')) ≫ a' := by
                    simp only [Category.assoc]
              _ = ((i ∣_ V') ≫ X'.homOfLE h) ≫ a' := by
                rw [morphismRestrict_homOfLE]
              _ = (i ∣_ V') ≫ X'.homOfLE h ≫ a' := by
                simp only [Category.assoc]
        ⟩
    exact ⟨sqV, by
      dsimp only [inducedConormalMap, restrictedConormalMap]
      -- This is the missing naturality of the scheme-level conormal map under
      -- the composable open restrictions determined by `h`.
      sorry⟩

end AlgebraicGeometry.Scheme.Hom.Deformation
