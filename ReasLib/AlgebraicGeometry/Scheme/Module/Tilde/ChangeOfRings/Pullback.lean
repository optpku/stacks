module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.ChangeOfRings.GlobalSections
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Algebra.Homology.Additive

/-!
# Pullback in affine change of rings

Pullback along an affine spectrum map is compared with extension of scalars.  This leaf is
independent of quasicoherent pushforward infrastructure.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.tilde.ChangeOfRings.Pullback

/-- The composite adjunction for affine tilde sheafification followed by pullback. -/
@[stacks 01I9 "tilde-pullback composite adjunction"]
noncomputable def adjunction
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) ⊣
      Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) :=
  (tilde.adjunction (R := R)).comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))

/-- The composite adjunction for extension of scalars followed by affine tilde sheafification. -/
@[stacks 01I9 "extension-of-scalars tilde adjunction"]
noncomputable def extendAdjunction
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    ModuleCat.extendScalars φ.hom ⋙ tilde.functor S ⊣
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom :=
  (ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S))

/-- The pullback adjunction transported to the restriction-of-scalars right adjoint. -/
@[stacks 01I9 "transported tilde-pullback adjunction"]
noncomputable def restrictAdjunction
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) ⊣
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom :=
  (adjunction φ).ofNatIsoRight (ModuleSpecΓ.pushforwardIso φ)

/-- Pullback along `Spec.map φ` canonically commutes with affine tilde sheafification and
extension of scalars. -/
@[stacks 01I9 "pullback"]
noncomputable def iso
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor S :=
  (restrictAdjunction φ).leftAdjointUniq (extendAdjunction φ)

/-- Extension of scalars followed by affine tilde sheafification preserves zero morphisms. -/
instance extendTilde_preservesZeroMorphisms
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    (ModuleCat.extendScalars.{u, u, u} φ.hom ⋙ tilde.functor S).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_iso (iso φ)

/-- Pullback of complexes of affine tilde sheaves agrees with extension of scalars
followed by degreewise tilde sheafification. -/
noncomputable def mapHomologicalComplexIso
    {R S : CommRingCat.{u}} (φ : R ⟶ S) {ι : Type*} (c : ComplexShape ι) :
    (tilde.functor R).mapHomologicalComplex c ⋙
        (Scheme.Modules.pullback (Spec.map φ)).mapHomologicalComplex c ≅
      (ModuleCat.extendScalars.{u, u, u} φ.hom).mapHomologicalComplex c ⋙
        (tilde.functor S).mapHomologicalComplex c :=
  @NatIso.mapHomologicalComplex _ _ _ _ _ _ _ _ _
    (inferInstance : (tilde.functor R ⋙
      Scheme.Modules.pullback (Spec.map φ)).PreservesZeroMorphisms)
    (extendTilde_preservesZeroMorphisms φ) (iso φ) c

/-- The hom component of `iso` is the mate of the extension-of-scalars unit. -/
@[simp, stacks 01I9 "pullback change-of-rings hom mate"]
theorem hom_app_homEquiv
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : ModuleCat R) :
    (restrictAdjunction φ).homEquiv _ _ ((iso φ).hom.app M) =
      (extendAdjunction φ).unit.app M := sorry

/-- The inverse component of `iso` is the mate of the transported pullback unit. -/
@[simp, stacks 01I9 "pullback change-of-rings inverse mate"]
theorem inv_app_homEquiv
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : ModuleCat R) :
    (extendAdjunction φ).homEquiv _ _ ((iso φ).inv.app M) =
      (restrictAdjunction φ).unit.app M := sorry

end AlgebraicGeometry.tilde.ChangeOfRings.Pullback
