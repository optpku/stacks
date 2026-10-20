module

public import ReasLib.Algebra.Category.ModuleCat.ExteriorAlgebra.RestrictScalars
public import ReasLib.Algebra.Category.ModuleCat.ExteriorPower.RestrictScalars
public import ReasLib.Algebra.Category.ModuleCat.Determinant

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Module.Determinant TensorProduct

noncomputable section

universe u

namespace ModuleCat.Determinant

variable {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂]
variable {M : ModuleCat.{u} R₁} {N : ModuleCat.{u} R₂}

/-- A scalar-restriction exterior-algebra map carries determinant elements to determinant
elements when the original module map becomes an isomorphism after extension of scalars. -/
theorem mapRestrictScalars_mem (φ : R₁ →+* R₂)
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N)
    [Module.Free R₁ M] [Module.Finite R₁ M]
    [Module.Free R₂ N] [Module.Finite R₂ N]
    [IsIso (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ f)]
    (x : det[R₁](M)) :
    ModuleCat.exteriorAlgebra.mapRestrictScalars φ f
        (x : ExteriorAlgebra R₁ M) ∈ det[R₂](N) := sorry

/-- The underlying function on determinant lines induced by a scalar-restriction morphism. -/
noncomputable def mapRestrictScalarsFun (φ : R₁ →+* R₂)
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N)
    [Module.Free R₁ M] [Module.Finite R₁ M]
    [Module.Free R₂ N] [Module.Finite R₂ N]
    [IsIso (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ f)] :
    det[R₁](M) → det[R₂](N) := fun x ↦
  ⟨ModuleCat.exteriorAlgebra.mapRestrictScalars φ f
      (x : ExteriorAlgebra R₁ M), mapRestrictScalars_mem φ f x⟩

/-- The determinant function along scalar restriction preserves addition. -/
theorem mapRestrictScalarsFun_add (φ : R₁ →+* R₂)
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N)
    [Module.Free R₁ M] [Module.Finite R₁ M]
    [Module.Free R₂ N] [Module.Finite R₂ N]
    [IsIso (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ f)]
    (x y : det[R₁](M)) :
    mapRestrictScalarsFun φ f (x + y) =
      mapRestrictScalarsFun φ f x + mapRestrictScalarsFun φ f y := sorry

/-- The determinant function along scalar restriction is semilinear over the ring map. -/
theorem mapRestrictScalarsFun_smul (φ : R₁ →+* R₂)
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N)
    [Module.Free R₁ M] [Module.Finite R₁ M]
    [Module.Free R₂ N] [Module.Finite R₂ N]
    [IsIso (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ f)]
    (r : R₁) (x : det[R₁](M)) :
    mapRestrictScalarsFun φ f (r • x) = φ r • mapRestrictScalarsFun φ f x := sorry

/-- The map on determinant lines induced by a finite-free module morphism that becomes an
isomorphism after extension of scalars. -/
noncomputable def mapRestrictScalars (φ : R₁ →+* R₂)
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N)
    [Module.Free R₁ M] [Module.Finite R₁ M]
    [Module.Free R₂ N] [Module.Finite R₂ N]
    [IsIso (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ f)] :
    ModuleCat.of R₁ det[R₁](M) ⟶
      (ModuleCat.restrictScalars φ).obj (ModuleCat.of R₂ det[R₂](N)) :=
  ModuleCat.semilinearMapAddEquiv φ (ModuleCat.of R₁ det[R₁](M))
    (ModuleCat.of R₂ det[R₂](N))
    { toFun := mapRestrictScalarsFun φ f
      map_add' := mapRestrictScalarsFun_add φ f
      map_smul' := mapRestrictScalarsFun_smul φ f }

/-- The determinant map is induced by the scalar-restriction map on exterior algebras. -/
theorem mapRestrictScalars_ι (φ : R₁ →+* R₂)
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N)
    [Module.Free R₁ M] [Module.Finite R₁ M]
    [Module.Free R₂ N] [Module.Finite R₂ N]
    [IsIso (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ f)]
    (x : det[R₁](M)) :
    ((mapRestrictScalarsFun φ f x : det[R₂](N)) : ExteriorAlgebra R₂ N) =
      ModuleCat.exteriorAlgebra.mapRestrictScalars φ f
        (x : ExteriorAlgebra R₁ M) := sorry

/-- Scalar extension of the determinant map is an isomorphism whenever scalar extension of the
original finite-free module map is an isomorphism. -/
noncomputable instance mapRestrictScalars_fromExtendScalars_isIso (φ : R₁ →+* R₂)
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N)
    [Module.Free R₁ M] [Module.Finite R₁ M]
    [Module.Free R₂ N] [Module.Finite R₂ N]
    [IsIso (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ f)] :
    IsIso (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ
      (mapRestrictScalars φ f)) := sorry

end ModuleCat.Determinant

end
