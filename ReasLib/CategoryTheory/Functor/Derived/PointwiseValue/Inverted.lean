/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Left
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Right

/-!
# Denominators Act Invertibly on Pointwise Derived Values

The map between two pointwise derived values induced by a denominator is invertible whenever
both endpoint values exist (Stacks 05SB).  The inverse is constructed explicitly by reindexing
the defining (co)limit diagram along the inverse of the localized denominator.  This local
statement does not require a globally defined or total derived functor.
-/

@[expose] public section

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D)

namespace RightDerived.Value

open Limits

/-- The naturality equation for the cocone giving the inverse of the pointwise right-derived
map along a denominator `f`: the legs reindex an arrow `S.Q.obj W ⟶ S.Q.obj Y` along the
inverse of the localized denominator `S.Q.obj X ≅ S.Q.obj Y`. -/
@[stacks 05SB]
theorem invCocone_naturality_raw {X Y : D} (f : X ⟶ Y) (hf : S f)
    [F.HasPointwiseRightDerivedFunctorAt S X]
    (g₁ g₂ : CostructuredArrow S.Q (S.Q.obj Y)) (φ : g₁ ⟶ g₂) :
    (CostructuredArrow.proj S.Q (S.Q.obj Y) ⋙ F).map φ ≫
      colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F)
          (CostructuredArrow.mk (g₂.hom ≫ (Localization.isoOfHom S.Q S f hf).inv)) =
      colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F)
        (CostructuredArrow.mk (g₁.hom ≫ (Localization.isoOfHom S.Q S f hf).inv)) ≫
          ((Functor.const (CostructuredArrow S.Q (S.Q.obj Y))).obj (obj F S X)).map φ := sorry

/-- The cocone on the right-derived-value diagram at `Y` whose leg at `g : S.Q.obj W ⟶ S.Q.obj Y`
is the colimit leg at `X` indexed by `g ≫ (S.Q.map f)⁻¹`; it induces the inverse of the
pointwise right-derived map along a denominator `f`. -/
@[stacks 05SB]
noncomputable def invCocone {X Y : D} (f : X ⟶ Y) (hf : S f)
    [F.HasPointwiseRightDerivedFunctorAt S X] :
    Cocone (CostructuredArrow.proj S.Q (S.Q.obj Y) ⋙ F) :=
  Cocone.mk (obj F S X)
    { app := fun g ↦
        colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F)
          (CostructuredArrow.mk (g.hom ≫ (Localization.isoOfHom S.Q S f hf).inv))
      naturality := fun g₁ g₂ φ ↦ invCocone_naturality_raw F S f hf g₁ g₂ φ }

/-- The isomorphism between pointwise right-derived values induced by a denominator: its
forward map is the canonical map `map F S f`, and its inverse is induced by reindexing colimit
legs along the inverse of the localized denominator. -/
@[stacks 05SB "denominator isomorphism on pointwise right-derived values"]
noncomputable def mapIsoOfMem {X Y : D} (f : X ⟶ Y) (hf : S f)
    [F.HasPointwiseRightDerivedFunctorAt S X]
    [F.HasPointwiseRightDerivedFunctorAt S Y] :
    obj F S X ≅ obj F S Y where
  hom := map F S f
  inv := colimit.desc _ (invCocone F S f hf)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- A denominator induces an isomorphism between its two pointwise right-derived values. -/
@[stacks 05SB "denominator inversion on pointwise right-derived values"]
theorem map_isIso_of_mem {X Y : D} (f : X ⟶ Y) (hf : S f)
    [F.HasPointwiseRightDerivedFunctorAt S X]
    [F.HasPointwiseRightDerivedFunctorAt S Y] :
    IsIso (map F S f) :=
  (mapIsoOfMem F S f hf).isIso_hom

/-- The forward map of a pointwise right-derived denominator isomorphism is the canonical
pointwise map. -/
@[simp, stacks 05SB "denominator isomorphism on pointwise right-derived values, hom"]
theorem mapIsoOfMem_hom {X Y : D} (f : X ⟶ Y) (hf : S f)
    [F.HasPointwiseRightDerivedFunctorAt S X]
    [F.HasPointwiseRightDerivedFunctorAt S Y] :
    (mapIsoOfMem F S f hf).hom = map F S f := rfl

/-- The inverse of a pointwise right-derived denominator isomorphism sends the colimit leg at
`g : S.Q.obj W ⟶ S.Q.obj Y` to the colimit leg at `g ≫ (S.Q.map f)⁻¹`. -/
@[reassoc (attr := simp), stacks 05SB
  "denominator isomorphism on pointwise right-derived values, inv"]
theorem ι_mapIsoOfMem_inv {X Y : D} (f : X ⟶ Y) (hf : S f)
    [F.HasPointwiseRightDerivedFunctorAt S X]
    [F.HasPointwiseRightDerivedFunctorAt S Y]
    (g : CostructuredArrow S.Q (S.Q.obj Y)) :
    colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj Y) ⋙ F) g ≫ (mapIsoOfMem F S f hf).inv =
      colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F)
        (CostructuredArrow.mk (g.hom ≫ (Localization.isoOfHom S.Q S f hf).inv)) :=
  colimit.ι_desc (invCocone F S f hf) g

end RightDerived.Value

namespace LeftDerived.Value

open Limits

/-- The naturality equation for the cone giving the inverse of the pointwise left-derived map
along a denominator `f`: the projections reindex an arrow `S.Q.obj X ⟶ S.Q.obj W` along the
inverse of the localized denominator `S.Q.obj X ≅ S.Q.obj Y`. -/
@[stacks 05SB]
theorem invCone_naturality_raw {X Y : D} (f : X ⟶ Y) (hf : S f)
    [F.HasPointwiseLeftDerivedFunctorAt S Y]
    (g₁ g₂ : StructuredArrow (S.Q.obj X) S.Q) (φ : g₁ ⟶ g₂) :
    ((Functor.const (StructuredArrow (S.Q.obj X) S.Q)).obj (obj F S Y)).map φ ≫
      limit.π (StructuredArrow.proj (S.Q.obj Y) S.Q ⋙ F)
        (StructuredArrow.mk ((Localization.isoOfHom S.Q S f hf).inv ≫ g₂.hom)) =
      limit.π (StructuredArrow.proj (S.Q.obj Y) S.Q ⋙ F)
          (StructuredArrow.mk ((Localization.isoOfHom S.Q S f hf).inv ≫ g₁.hom)) ≫
        (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F).map φ := sorry

/-- The cone on the left-derived-value diagram at `X` whose projection at
`g : S.Q.obj X ⟶ S.Q.obj W` is the limit projection at `Y` indexed by `(S.Q.map f)⁻¹ ≫ g`; it
induces the inverse of the pointwise left-derived map along a denominator `f`. -/
@[stacks 05SB]
noncomputable def invCone {X Y : D} (f : X ⟶ Y) (hf : S f)
    [F.HasPointwiseLeftDerivedFunctorAt S Y] :
    Cone (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F) :=
  Cone.mk (obj F S Y)
    { app := fun g ↦
        limit.π (StructuredArrow.proj (S.Q.obj Y) S.Q ⋙ F)
          (StructuredArrow.mk ((Localization.isoOfHom S.Q S f hf).inv ≫ g.hom))
      naturality := fun g₁ g₂ φ ↦ invCone_naturality_raw F S f hf g₁ g₂ φ }

/-- The isomorphism between pointwise left-derived values induced by a denominator: its forward
map is the canonical map `map F S f`, and its inverse is induced by reindexing limit projections
along the inverse of the localized denominator. -/
@[stacks 05SB "denominator isomorphism on pointwise left-derived values"]
noncomputable def mapIsoOfMem {X Y : D} (f : X ⟶ Y) (hf : S f)
    [F.HasPointwiseLeftDerivedFunctorAt S X]
    [F.HasPointwiseLeftDerivedFunctorAt S Y] :
    obj F S X ≅ obj F S Y where
  hom := map F S f
  inv := limit.lift _ (invCone F S f hf)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- A denominator induces an isomorphism between its two pointwise left-derived values. -/
@[stacks 05SB "denominator inversion on pointwise left-derived values"]
theorem map_isIso_of_mem {X Y : D} (f : X ⟶ Y) (hf : S f)
    [F.HasPointwiseLeftDerivedFunctorAt S X]
    [F.HasPointwiseLeftDerivedFunctorAt S Y] :
    IsIso (map F S f) :=
  (mapIsoOfMem F S f hf).isIso_hom

/-- The forward map of a pointwise left-derived denominator isomorphism is the canonical
pointwise map. -/
@[simp, stacks 05SB "denominator isomorphism on pointwise left-derived values, hom"]
theorem mapIsoOfMem_hom {X Y : D} (f : X ⟶ Y) (hf : S f)
    [F.HasPointwiseLeftDerivedFunctorAt S X]
    [F.HasPointwiseLeftDerivedFunctorAt S Y] :
    (mapIsoOfMem F S f hf).hom = map F S f := rfl

/-- The inverse of a pointwise left-derived denominator isomorphism followed by the limit
projection at `g : S.Q.obj X ⟶ S.Q.obj W` is the limit projection at `(S.Q.map f)⁻¹ ≫ g`. -/
@[reassoc (attr := simp), stacks 05SB
  "denominator isomorphism on pointwise left-derived values, inv"]
theorem mapIsoOfMem_inv_π {X Y : D} (f : X ⟶ Y) (hf : S f)
    [F.HasPointwiseLeftDerivedFunctorAt S X]
    [F.HasPointwiseLeftDerivedFunctorAt S Y]
    (g : StructuredArrow (S.Q.obj X) S.Q) :
    (mapIsoOfMem F S f hf).inv ≫ limit.π (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F) g =
      limit.π (StructuredArrow.proj (S.Q.obj Y) S.Q ⋙ F)
        (StructuredArrow.mk ((Localization.isoOfHom S.Q S f hf).inv ≫ g.hom)) :=
  limit.lift_π (invCone F S f hf) g

end LeftDerived.Value

end CategoryTheory.Functor
