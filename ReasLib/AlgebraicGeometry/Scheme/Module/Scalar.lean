module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Module.Equiv.Basic

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {S : Scheme.{u}}

/-- Multiplication by the restriction of a global unit is an isomorphism on sections
of a scheme module over each open subset. -/
noncomputable def unitScalarIsoApp (M : S.Modules) (a : Γ(S, ⊤)ˣ) (U : S.Opens) :
    M.val.obj (.op U) ≅ M.val.obj (.op U) :=
  (LinearEquiv.smulOfUnit (R := Γ(S, U)) (M := M.val.obj (.op U))
    (Units.map (S.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom a)).toModuleIso

/-- Multiplication by the restrictions of a global unit commutes with restriction
maps of a scheme module. -/
theorem unitScalarIsoApp_naturality (M : S.Modules) (a : Γ(S, ⊤)ˣ)
    {U V : S.Opensᵒᵖ} (restriction : U ⟶ V) :
    M.val.map restriction ≫
        (ModuleCat.restrictScalars (S.ringCatSheaf.obj.map restriction).hom).map
          (unitScalarIsoApp M a V.unop).hom =
      (unitScalarIsoApp M a U.unop).hom ≫ M.val.map restriction := sorry

/-- Multiplication by a global unit defines an automorphism of a scheme module. -/
noncomputable def unitScalarIso (M : S.Modules) (a : Γ(S, ⊤)ˣ) : M ≅ M :=
  (SheafOfModules.fullyFaithfulForget S.ringCatSheaf).preimageIso
    (PresheafOfModules.isoMk (fun U ↦ unitScalarIsoApp M a U.unop)
      (fun {_ _} restriction ↦ unitScalarIsoApp_naturality M a restriction))

/-- The automorphism given by a global unit multiplies every local section by
the restriction of that unit. -/
theorem unitScalarIso_hom_app (M : S.Modules) (a : Γ(S, ⊤)ˣ)
    (U : S.Opens) (localSection : Γ(M, U)) :
    (unitScalarIso M a).hom.app U localSection =
      S.presheaf.map (homOfLE le_top : U ⟶ ⊤).op a.val • localSection := sorry

end AlgebraicGeometry.Scheme.Modules
