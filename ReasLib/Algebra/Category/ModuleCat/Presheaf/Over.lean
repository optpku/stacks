/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Restriction
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Restriction of module presheaves to slice categories

This leaf owns the object- and morphism-level restriction of a module presheaf to a slice category.
It is independent of compatible-section constructions.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w z

namespace PresheafOfModules

variable {D : Type u} [Category.{v} D] {R : Dᵒᵖ ⥤ RingCat.{w}}

variable (R) in
/-- The restriction functor from module presheaves on `D` to module presheaves on `D / U`. -/
noncomputable def overFunctor (U : D) :
    PresheafOfModules.{z} R ⥤ PresheafOfModules.{z} ((Over.forget U).op ⋙ R) :=
  pushforward (𝟙 _)

/-- The restriction of a module presheaf to the slice category `D / U`. -/
noncomputable abbrev over (M : PresheafOfModules.{z} R) (U : D) :
    PresheafOfModules.{z} ((Over.forget U).op ⋙ R) :=
  (overFunctor R U).obj M

/-- The restriction of a module-presheaf morphism to the slice category `D / U`. -/
noncomputable abbrev Hom.over {M N : PresheafOfModules.{z} R} (ψ : M ⟶ N) (U : D) :
    M.over U ⟶ N.over U :=
  (overFunctor R U).map ψ

namespace Restriction

variable (R : Dᵒᵖ ⥤ RingCat.{w}) (U : D)

/-- The objectwise comparison from slice restriction to plain precomposition. -/
noncomputable def overAppIso (M : PresheafOfModules.{z} R) (X : (Over U)ᵒᵖ) :
    (M.over U).obj X ≅ M.obj ((Over.forget U).op.obj X) :=
  (idComponentApp' (𝟙 ((Over.forget U).op ⋙ R)) rfl
    ((PresheafOfModules.pushforward₀ (Over.forget U) R).obj M) X).symm

/-- The objectwise comparisons from slice restriction to plain precomposition commute with
restriction maps in the slice. -/
theorem overAppIso_naturality (M : PresheafOfModules.{z} R)
    {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y) :
    (M.over U).map f ≫
        (ModuleCat.restrictScalars ((((Over.forget U).op ⋙ R).map f).hom)).map
          (overAppIso R U M Y).hom =
      (overAppIso R U M X).hom ≫
        ((PresheafOfModules.pushforward₀ (Over.forget U) R).obj M).map f := sorry

/-- Restriction of one module presheaf to `D / U`, compared with its plain precomposition by
the forgetful functor. -/
@[stacks 03EJ "presheaf restriction to a slice as precomposition"]
noncomputable def overIso (M : PresheafOfModules.{z} R) :
    M.over U ≅ (PresheafOfModules.pushforward₀ (Over.forget U) R).obj M :=
  PresheafOfModules.isoMk (overAppIso R U M)
    (fun _ _ f ↦ overAppIso_naturality R U M f)

/-- The slice-restriction comparison is natural in the module presheaf. -/
theorem overIso_naturality {M N : PresheafOfModules.{z} R} (f : M ⟶ N) :
    Hom.over f U ≫ (overIso R U N).hom =
      (overIso R U M).hom ≫
        (PresheafOfModules.pushforward₀ (Over.forget U) R).map f := sorry

/-- The inverse slice-restriction comparison is natural in the module presheaf. -/
@[stacks 03EJ "inverse naturality of slice restriction"]
theorem overIso_inv_naturality {M N : PresheafOfModules.{z} R} (f : M ⟶ N) :
    (PresheafOfModules.pushforward₀ (Over.forget U) R).map f ≫
        (overIso R U N).inv =
      (overIso R U M).inv ≫ Hom.over f U := sorry

/-- The forward slice-restriction comparisons form a natural transformation. -/
@[stacks 03EJ "forward slice restriction natural transformation"]
noncomputable def overNatTrans :
    overFunctor R U ⟶ PresheafOfModules.pushforward₀ (Over.forget U) R where
  app M := (overIso R U M).hom
  naturality _ _ f := overIso_naturality R U f

/-- The inverse slice-restriction comparisons form the inverse natural transformation. -/
@[stacks 03EJ "inverse slice restriction natural transformation"]
noncomputable def overInvNatTrans :
    PresheafOfModules.pushforward₀ (Over.forget U) R ⟶ overFunctor R U where
  app M := (overIso R U M).inv
  naturality _ _ f := overIso_inv_naturality R U f

/-- A component of the forward slice-restriction natural transformation is `overIso`. -/
@[simp, stacks 03EJ "forward slice restriction natural transformation component"]
theorem overNatTrans_app (M : PresheafOfModules.{z} R) :
    (overNatTrans R U).app M = (overIso R U M).hom := sorry

/-- A component of the inverse slice-restriction natural transformation is the inverse of
`overIso`. -/
@[simp, stacks 03EJ "inverse slice restriction natural transformation component"]
theorem overInvNatTrans_app (M : PresheafOfModules.{z} R) :
    (overInvNatTrans R U).app M = (overIso R U M).inv := sorry

/-- The forward slice-restriction natural transformation followed by its inverse is the identity.
-/
@[simp, stacks 03EJ "slice restriction natural transformation forward-inverse law"]
theorem overNatTrans_hom_inv_id :
    overNatTrans R U ≫ overInvNatTrans R U = 𝟙 _ := sorry

/-- The inverse slice-restriction natural transformation followed by its forward map is the
identity. -/
@[simp, stacks 03EJ "slice restriction natural transformation inverse-forward law"]
theorem overNatTrans_inv_hom_id :
    overInvNatTrans R U ≫ overNatTrans R U = 𝟙 _ := sorry

/-- Restriction to `D / U` is naturally isomorphic to plain precomposition by the forgetful
functor.  This comparison removes the identity restriction of scalars retained by
`PresheafOfModules.pushforward`. -/
@[stacks 03EJ "natural presheaf restriction to a slice as precomposition"]
noncomputable def overNatIso :
    overFunctor R U ≅ PresheafOfModules.pushforward₀ (Over.forget U) R :=
  { hom := overNatTrans R U
    inv := overInvNatTrans R U
    hom_inv_id := overNatTrans_hom_inv_id R U
    inv_hom_id := overNatTrans_inv_hom_id R U }

/-- The forward natural transformation of `overNatIso` is explicit. -/
@[simp, stacks 03EJ "slice restriction natural isomorphism hom"]
theorem overNatIso_hom :
    (overNatIso R U).hom = overNatTrans R U := sorry

/-- The inverse natural transformation of `overNatIso` is explicit. -/
@[simp, stacks 03EJ "slice restriction natural isomorphism inverse"]
theorem overNatIso_inv :
    (overNatIso R U).inv = overInvNatTrans R U := sorry

/-- A component of `overNatIso` is the objectwise slice-restriction comparison. -/
@[simp, stacks 03EJ "slice restriction natural isomorphism component"]
theorem overNatIso_app (M : PresheafOfModules.{z} R) :
    (overNatIso R U).app M = overIso R U M := sorry

/-- The forward component of `overNatIso` is the forward objectwise comparison. -/
@[simp, stacks 03EJ "slice restriction natural isomorphism hom component"]
theorem overNatIso_hom_app (M : PresheafOfModules.{z} R) :
    (overNatIso R U).hom.app M = (overIso R U M).hom := sorry

/-- The inverse component of `overNatIso` is the inverse objectwise comparison. -/
@[simp, stacks 03EJ "slice restriction natural isomorphism inverse component"]
theorem overNatIso_inv_app (M : PresheafOfModules.{z} R) :
    (overNatIso R U).inv.app M = (overIso R U M).inv := sorry

end Restriction



end PresheafOfModules
