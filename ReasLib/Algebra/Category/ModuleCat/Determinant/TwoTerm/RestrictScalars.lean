module

public import ReasLib.Algebra.Category.ModuleCat.Determinant.RestrictScalars
public import ReasLib.Algebra.Category.ModuleCat.Determinant.TwoTerm

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Module.Determinant TensorProduct

noncomputable section

universe u

namespace ModuleCat.TwoTermDeterminant

variable {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂]
variable {N₁ M₁ : ModuleCat.{u} R₁} {N₂ M₂ : ModuleCat.{u} R₂}

/-- The underlying transport of a linear map between determinant lines across two scalar-change
isomorphisms. -/
noncomputable def mapRestrictScalarsFun (φ : R₁ →+* R₂)
    (fN : N₁ ⟶ (ModuleCat.restrictScalars φ).obj N₂)
    (fM : M₁ ⟶ (ModuleCat.restrictScalars φ).obj M₂)
    [Module.Free R₁ N₁] [Module.Finite R₁ N₁]
    [Module.Free R₂ N₂] [Module.Finite R₂ N₂]
    [Module.Free R₁ M₁] [Module.Finite R₁ M₁]
    [Module.Free R₂ M₂] [Module.Finite R₂ M₂]
    [IsIso (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ fN)]
    [IsIso (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ fM)]
    (a : det[R₁](N₁) →ₗ[R₁] det[R₁](M₁)) :
    det[R₂](N₂) →ₗ[R₂] det[R₂](M₂) :=
  (inv (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ
        (ModuleCat.Determinant.mapRestrictScalars φ fN)) ≫
      (ModuleCat.extendScalars φ).map (ModuleCat.ofHom a) ≫
      ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ
        (ModuleCat.Determinant.mapRestrictScalars φ fM)).hom

/-- Transport of maps between two-term determinant lines preserves addition. -/
theorem mapRestrictScalarsFun_add (φ : R₁ →+* R₂)
    (fN : N₁ ⟶ (ModuleCat.restrictScalars φ).obj N₂)
    (fM : M₁ ⟶ (ModuleCat.restrictScalars φ).obj M₂)
    [Module.Free R₁ N₁] [Module.Finite R₁ N₁]
    [Module.Free R₂ N₂] [Module.Finite R₂ N₂]
    [Module.Free R₁ M₁] [Module.Finite R₁ M₁]
    [Module.Free R₂ M₂] [Module.Finite R₂ M₂]
    [IsIso (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ fN)]
    [IsIso (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ fM)]
    (a b : det[R₁](N₁) →ₗ[R₁] det[R₁](M₁)) :
    mapRestrictScalarsFun φ fN fM (a + b) =
      mapRestrictScalarsFun φ fN fM a + mapRestrictScalarsFun φ fN fM b := sorry

/-- Transport of maps between two-term determinant lines is semilinear over the ring map. -/
theorem mapRestrictScalarsFun_smul (φ : R₁ →+* R₂)
    (fN : N₁ ⟶ (ModuleCat.restrictScalars φ).obj N₂)
    (fM : M₁ ⟶ (ModuleCat.restrictScalars φ).obj M₂)
    [Module.Free R₁ N₁] [Module.Finite R₁ N₁]
    [Module.Free R₂ N₂] [Module.Finite R₂ N₂]
    [Module.Free R₁ M₁] [Module.Finite R₁ M₁]
    [Module.Free R₂ M₂] [Module.Finite R₂ M₂]
    [IsIso (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ fN)]
    [IsIso (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ fM)]
    (r : R₁) (a : det[R₁](N₁) →ₗ[R₁] det[R₁](M₁)) :
    mapRestrictScalarsFun φ fN fM (r • a) =
      φ r • mapRestrictScalarsFun φ fN fM a := sorry

/-- Scalar-change transport on the module of maps between two determinant lines. -/
noncomputable def mapRestrictScalars (φ : R₁ →+* R₂)
    (fN : N₁ ⟶ (ModuleCat.restrictScalars φ).obj N₂)
    (fM : M₁ ⟶ (ModuleCat.restrictScalars φ).obj M₂)
    [Module.Free R₁ N₁] [Module.Finite R₁ N₁]
    [Module.Free R₂ N₂] [Module.Finite R₂ N₂]
    [Module.Free R₁ M₁] [Module.Finite R₁ M₁]
    [Module.Free R₂ M₂] [Module.Finite R₂ M₂]
    [IsIso (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ fN)]
    [IsIso (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ fM)] :
    ModuleCat.of R₁ (det[R₁](N₁) →ₗ[R₁] det[R₁](M₁)) ⟶
      (ModuleCat.restrictScalars φ).obj
        (ModuleCat.of R₂ (det[R₂](N₂) →ₗ[R₂] det[R₂](M₂))) :=
  ModuleCat.semilinearMapAddEquiv φ
    (ModuleCat.of R₁ (det[R₁](N₁) →ₗ[R₁] det[R₁](M₁)))
    (ModuleCat.of R₂ (det[R₂](N₂) →ₗ[R₂] det[R₂](M₂)))
    { toFun := mapRestrictScalarsFun φ fN fM
      map_add' := mapRestrictScalarsFun_add φ fN fM
      map_smul' := mapRestrictScalarsFun_smul φ fN fM }

/-- Evaluation after determinant-line transport agrees with the two determinant base-change
maps. -/
theorem mapRestrictScalars_apply (φ : R₁ →+* R₂)
    (fN : N₁ ⟶ (ModuleCat.restrictScalars φ).obj N₂)
    (fM : M₁ ⟶ (ModuleCat.restrictScalars φ).obj M₂)
    [Module.Free R₁ N₁] [Module.Finite R₁ N₁]
    [Module.Free R₂ N₂] [Module.Finite R₂ N₂]
    [Module.Free R₁ M₁] [Module.Finite R₁ M₁]
    [Module.Free R₂ M₂] [Module.Finite R₂ M₂]
    [IsIso (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ fN)]
    [IsIso (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ fM)]
    (a : det[R₁](N₁) →ₗ[R₁] det[R₁](M₁)) (x : det[R₁](N₁)) :
    ModuleCat.Determinant.mapRestrictScalarsFun φ fM (a x) =
      mapRestrictScalarsFun φ fN fM a
        (ModuleCat.Determinant.mapRestrictScalarsFun φ fN x) := sorry

/-- The evaluation equation uniquely characterizes scalar-change transport between two-term
determinant lines. -/
theorem mapRestrictScalars_unique (φ : R₁ →+* R₂)
    (fN : N₁ ⟶ (ModuleCat.restrictScalars φ).obj N₂)
    (fM : M₁ ⟶ (ModuleCat.restrictScalars φ).obj M₂)
    [Module.Free R₁ N₁] [Module.Finite R₁ N₁]
    [Module.Free R₂ N₂] [Module.Finite R₂ N₂]
    [Module.Free R₁ M₁] [Module.Finite R₁ M₁]
    [Module.Free R₂ M₂] [Module.Finite R₂ M₂]
    [IsIso (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ fN)]
    [IsIso (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ fM)]
    (a : det[R₁](N₁) →ₗ[R₁] det[R₁](M₁))
    (b : det[R₂](N₂) →ₗ[R₂] det[R₂](M₂))
    (h : ∀ x, b (ModuleCat.Determinant.mapRestrictScalars φ fN x) =
      ModuleCat.Determinant.mapRestrictScalars φ fM (a x)) :
    b = mapRestrictScalars φ fN fM a := sorry

/-- The two-term discriminant commutes with scalar change along a commuting square of
differentials. -/
theorem mapRestrictScalars_twoTermDiscriminant (φ : R₁ →+* R₂)
    (d₁ : N₁ ⟶ M₁) (d₂ : N₂ ⟶ M₂)
    (fN : N₁ ⟶ (ModuleCat.restrictScalars φ).obj N₂)
    (fM : M₁ ⟶ (ModuleCat.restrictScalars φ).obj M₂)
    (hcomm : d₁ ≫ fM = fN ≫ (ModuleCat.restrictScalars φ).map d₂)
    [Module.Free R₁ N₁] [Module.Finite R₁ N₁]
    [Module.Free R₂ N₂] [Module.Finite R₂ N₂]
    [Module.Free R₁ M₁] [Module.Finite R₁ M₁]
    [Module.Free R₂ M₂] [Module.Finite R₂ M₂]
    [IsIso (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ fN)]
    [IsIso (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ fM)]
    (hRank₁ : Module.finrank R₁ N₁ = Module.finrank R₁ M₁)
    (hRank₂ : Module.finrank R₂ N₂ = Module.finrank R₂ M₂) :
    mapRestrictScalars φ fN fM (ModuleCat.twoTermDiscriminant d₁ hRank₁) =
      ModuleCat.twoTermDiscriminant d₂ hRank₂ := sorry

end ModuleCat.TwoTermDeterminant

end
