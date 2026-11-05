module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Global sections in affine change of rings

This leaf owns the global-sections comparisons shared by the pullback and pushforward sides.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ModuleSpecΓ

/-- Global sections identify pushforward along `Spec.map φ` with restriction of scalars. -/
@[stacks 01I9 "global sections of pushforward"]
noncomputable def pushforwardIso
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom :=
  Functor.isoWhiskerRight (pushforwardCompModulesSpecToSheafIso φ)
    (TopCat.Sheaf.forget (ModuleCat R) (Spec R) ⋙ (evaluation _ _).obj (.op ⊤))

end AlgebraicGeometry.ModuleSpecΓ

namespace AlgebraicGeometry.tilde.ChangeOfRings.GlobalSections

/-- The global-sections comparison specialized to affine tilde sheaves. -/
@[stacks 01I9 "global sections of pushforward tilde"]
noncomputable def pushforwardIso
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    (tilde.functor S ⋙ Scheme.Modules.pushforward (Spec.map φ)) ⋙
        moduleSpecΓFunctor (R := R) ≅
      ModuleCat.restrictScalars φ.hom :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (tilde.functor S) (ModuleSpecΓ.pushforwardIso φ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (tilde.toTildeΓNatIso (R := S)).symm
      (ModuleCat.restrictScalars φ.hom) ≪≫
    Functor.leftUnitor _

end AlgebraicGeometry.tilde.ChangeOfRings.GlobalSections
