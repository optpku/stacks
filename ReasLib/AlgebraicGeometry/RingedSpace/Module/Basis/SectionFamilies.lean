module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.Topology.Sheaves.Basis.Algebraic.SectionFamilies

/-!
# Module-linear two-basis section families on ringed spaces

This module adds the module-linearity condition and extension theorem for the generic
`TopCat.Presheaf.BasisPushforwardHomFamily` associated to a morphism of ringed spaces.
-/

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.BasisPushforwardHomFamily

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable {BX : Set (Opens X)} {BY : Set (Opens Y)}
variable (ℱ : X.Modules)
variable (𝒢 : Y.Modules)

/-- A two-basis section family is linear over `𝒪_Y(V)` through the structure-sheaf map induced
by `f` and restriction from `f⁻¹(V)` to `U`. -/
def IsLinear
    {ℱ : X.Modules} {𝒢 : Y.Modules}
    (η : TopCat.Presheaf.BasisPushforwardHomFamily f.hom.base BX BY
      ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf Y)).obj 𝒢).obj
      ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj ℱ).obj) : Prop :=
  ∀ (U : BasisOpen BX) (V : BasisOpen BY)
    (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj)
    (r : (RingedSpace.ringCatSheaf Y).obj.obj (op V.obj))
    (s : 𝒢.val.presheaf.obj (op V.obj)),
    (η.app U V hUV : 𝒢.val.presheaf.obj (op V.obj) → ℱ.val.presheaf.obj (op U.obj))
        (r • s) =
      ((ℱ.val.obj (op U.obj)).smul
        (((RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj) ≫
          (RingedSpace.ringCatSheaf X).obj.map (homOfLE hUV).op) r)).hom
        (η.app U V hUV s)

/-- A compatible two-basis family equipped with its module-linearity condition.

The underlying section-family data remains the generic
`TopCat.Presheaf.BasisPushforwardHomFamily`; this subtype is the module-specific layer needed
for the equivalence with morphisms of module sheaves. -/
abbrev LinearFamily
    {ℱ : X.Modules} {𝒢 : Y.Modules} :=
  {η : TopCat.Presheaf.BasisPushforwardHomFamily f.hom.base BX BY
      ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf Y)).obj 𝒢).obj
      ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj ℱ).obj //
    IsLinear f η}

/-- The two-basis family induced by a morphism of module sheaves is linear. -/
theorem ofHom_isLinear
    {ℱ : X.Modules} {𝒢 : Y.Modules}
    (φ : 𝒢 ⟶ (pushforward f).obj ℱ) :
    IsLinear (BX := BX) (BY := BY) f
      (TopCat.Presheaf.BasisPushforwardHomFamily.ofHom f.hom.base (BX := BX) (BY := BY)
        ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf Y)).map φ)) := sorry

/-- Restrict a morphism of module sheaves to its compatible linear family on two bases. -/
def ofHom
    {ℱ : X.Modules} {𝒢 : Y.Modules}
    (φ : 𝒢 ⟶ (pushforward f).obj ℱ) :
    LinearFamily (BX := BX) (BY := BY) (ℱ := ℱ) (𝒢 := 𝒢) f :=
  ⟨TopCat.Presheaf.BasisPushforwardHomFamily.ofHom f.hom.base (BX := BX) (BY := BY)
      ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf Y)).map φ),
    ofHom_isLinear (BX := BX) (BY := BY) f φ⟩

/-- A component of `ofHom` is the restriction of the corresponding module-sheaf morphism. -/
@[simp]
theorem ofHom_app
    {ℱ : X.Modules} {𝒢 : Y.Modules}
    (φ : 𝒢 ⟶ (pushforward f).obj ℱ)
    (U : BasisOpen BX) (V : BasisOpen BY)
    (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj) :
    (ofHom (BX := BX) (BY := BY) f φ).val.app U V hUV =
      ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf Y)).map φ).hom.app (op V.obj) ≫
        ℱ.val.presheaf.map (homOfLE hUV).op := sorry

/-- The morphism of underlying abelian sheaves extending a compatible linear two-basis family,
constructed by `TopCat.Presheaf.BasisPushforwardHomFamily.toHom`. -/
noncomputable abbrev toSheafHom
    {ℱ : X.Modules} {𝒢 : Y.Modules}
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (η : LinearFamily (BX := BX) (BY := BY) (ℱ := ℱ) (𝒢 := 𝒢) f) :
    (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf Y)).obj 𝒢 ⟶
      (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf Y)).obj ((pushforward f).obj ℱ) :=
  TopCat.Presheaf.BasisPushforwardHomFamily.toHom f.hom.base hBX hBY η.val

/-- The abelian extension of a linear two-basis family is linear over `𝒪_Y` on every open. -/
theorem toSheafHom_map_smul
    {ℱ : X.Modules} {𝒢 : Y.Modules}
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (η : LinearFamily (BX := BX) (BY := BY) (ℱ := ℱ) (𝒢 := 𝒢) f)
    (V : (Opens Y)ᵒᵖ) (r : (RingedSpace.ringCatSheaf Y).obj.obj V) (s : 𝒢.val.obj V) :
    ((toSheafHom f hBX hBY η).hom : 𝒢.val.presheaf ⟶ ((pushforward f).obj ℱ).val.presheaf).app V
        (r • s) =
      SMul.smul (α := ((pushforward f).obj ℱ).val.presheaf.obj V) r
        (((toSheafHom f hBX hBY η).hom :
          𝒢.val.presheaf ⟶ ((pushforward f).obj ℱ).val.presheaf).app V s) := sorry
/- Proof strategy: both sides are sections of `ℱ` over `f⁻¹(V)`; by the sheaf condition it
suffices to compare restrictions to basis opens `U ⊆ f⁻¹(W)` for basis opens `W ⊆ V`, where
`TopCat.Presheaf.BasisPushforwardHomFamily.toHom_app` reduces the claim to `η.property`. -/

/-- Extend a compatible linear two-basis family to its uniquely determined morphism of module
sheaves into the pushforward: the underlying abelian extension `toSheafHom` together with its
`𝒪_Y`-linearity. -/
noncomputable def toHom
    {ℱ : X.Modules} {𝒢 : Y.Modules}
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (η : LinearFamily (BX := BX) (BY := BY) (ℱ := ℱ) (𝒢 := 𝒢) f) :
    𝒢 ⟶ (pushforward f).obj ℱ :=
  ⟨PresheafOfModules.homMk (toSheafHom f hBX hBY η).hom (toSheafHom_map_smul f hBX hBY η)⟩

/-- The module-sheaf morphism selected by `toHom` restricts to the prescribed linear family. -/
theorem toHom_app
    {ℱ : X.Modules} {𝒢 : Y.Modules}
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (η : LinearFamily (BX := BX) (BY := BY) (ℱ := ℱ) (𝒢 := 𝒢) f)
    (U : BasisOpen BX) (V : BasisOpen BY)
    (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj) :
    ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf Y)).map
        (toHom (BX := BX) (BY := BY) (ℱ := ℱ) (𝒢 := 𝒢) f hBX hBY η)).hom.app (op V.obj) ≫
        ℱ.val.presheaf.map (homOfLE hUV).op =
      η.val.app U V hUV :=
  TopCat.Presheaf.BasisPushforwardHomFamily.toHom_app f.hom.base hBX hBY η.val U V hUV

/-- A module-sheaf morphism with the prescribed two-basis family is `toHom f hBX hBY η`. -/
theorem toHom_unique
    {ℱ : X.Modules} {𝒢 : Y.Modules}
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (η : LinearFamily (BX := BX) (BY := BY) (ℱ := ℱ) (𝒢 := 𝒢) f)
    (φ : 𝒢 ⟶ (pushforward f).obj ℱ)
    (hφ : ∀ (U : BasisOpen BX) (V : BasisOpen BY)
      (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj),
      ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf Y)).map φ).hom.app (op V.obj) ≫
          ℱ.val.presheaf.map (homOfLE hUV).op =
        η.val.app U V hUV) :
    φ = toHom (BX := BX) (BY := BY) (ℱ := ℱ) (𝒢 := 𝒢) f hBX hBY η := sorry

/-- A compatible linear two-basis family extends uniquely to a morphism of module sheaves into
the pushforward. -/
theorem existsUniquePushforwardHom
    {ℱ : X.Modules} {𝒢 : Y.Modules}
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (η : LinearFamily (BX := BX) (BY := BY) (ℱ := ℱ) (𝒢 := 𝒢) f) :
    ∃! φ : 𝒢 ⟶ (pushforward f).obj ℱ,
      ∀ (U : BasisOpen BX) (V : BasisOpen BY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj),
        ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf Y)).map φ).hom.app (op V.obj) ≫
            ℱ.val.presheaf.map (homOfLE hUV).op =
          η.val.app U V hUV :=
  ⟨toHom f hBX hBY η, toHom_app f hBX hBY η, toHom_unique f hBX hBY η⟩

/-- A raw compatible two-basis family together with a linearity proof extends uniquely to a
morphism from a module sheaf on `Y` to the pushforward of a module sheaf on `X`. -/
theorem existsUniquePushforwardHom_of_isLinear
    {ℱ : X.Modules} {𝒢 : Y.Modules}
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (η : TopCat.Presheaf.BasisPushforwardHomFamily f.hom.base BX BY
      ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf Y)).obj 𝒢).obj
      ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj ℱ).obj)
    (hη : IsLinear f η) :
    ∃! φ : 𝒢 ⟶ (pushforward f).obj ℱ,
      ∀ (U : BasisOpen BX) (V : BasisOpen BY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj),
        ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf Y)).map φ).hom.app (op V.obj) ≫
            ℱ.val.presheaf.map (homOfLE hUV).op =
          η.app U V hUV :=
  existsUniquePushforwardHom f hBX hBY ⟨η, hη⟩

/-- Extending the linear two-basis restriction of a module-sheaf morphism recovers that
morphism. -/
@[simp]
theorem toHom_ofHom
    {ℱ : X.Modules} {𝒢 : Y.Modules}
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (φ : 𝒢 ⟶ (pushforward f).obj ℱ) :
    toHom (BX := BX) (BY := BY) (ℱ := ℱ) (𝒢 := 𝒢) f hBX hBY
      (ofHom (BX := BX) (BY := BY) f φ) = φ := sorry

/-- Restricting the extension of a compatible linear family recovers that family. -/
@[simp]
theorem ofHom_toHom
    {ℱ : X.Modules} {𝒢 : Y.Modules}
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (η : LinearFamily (BX := BX) (BY := BY) (ℱ := ℱ) (𝒢 := 𝒢) f) :
    ofHom (BX := BX) (BY := BY) f
      (toHom (BX := BX) (BY := BY) (ℱ := ℱ) (𝒢 := 𝒢) f hBX hBY η) = η := sorry

/-- The canonical equivalence between morphisms of module sheaves into a pushforward and
compatible linear two-basis section families. -/
noncomputable def homEquiv
    {ℱ : X.Modules} {𝒢 : Y.Modules}
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY) :
    (𝒢 ⟶ (pushforward f).obj ℱ) ≃ LinearFamily (BX := BX) (BY := BY) (ℱ := ℱ) (𝒢 := 𝒢) f where
  toFun := ofHom (BX := BX) (BY := BY) f
  invFun := toHom (BX := BX) (BY := BY) (ℱ := ℱ) (𝒢 := 𝒢) f hBX hBY
  left_inv := toHom_ofHom (BX := BX) (BY := BY) (ℱ := ℱ) (𝒢 := 𝒢) f hBX hBY
  right_inv := ofHom_toHom (BX := BX) (BY := BY) (ℱ := ℱ) (𝒢 := 𝒢) f hBX hBY

end AlgebraicGeometry.RingedSpace.Module.BasisPushforwardHomFamily
