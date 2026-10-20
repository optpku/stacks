module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.OpenImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PresentationRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.ExtensionByZero
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Integer
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.IntegerDegree

/-!
# Restriction maps in étale cohomology of algebraic spaces

An open immersion `ι : U ⟶ X` of algebraic spaces induces a restriction morphism
`H^q(X, F) ⟶ H^q(U, F|_U)` on étale cohomology of `𝒪_X`-modules, obtained by
precomposition with the extension-by-zero trace, transport along étale restriction,
and the identification of `toSheaf (Modules.restrict F ι)` with étale sheaf restriction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The comparison `ℤ̲_U ⟶ ι⁻¹ ℤ̲_X` obtained by sheafifying the identification of
constant presheaves along an open immersion. -/
noncomputable def cohomologyIntegerPullbackHom {X U : AlgebraicSpace S}
    (ι : U ⟶ X) [IsOpenImmersion ι] :
    constantIntegerSheaf (smallEtaleTopology U) ⟶
      (etaleRestrictionSheaf ι AddCommGrpCat.{u}).obj (constantIntegerSheaf (smallEtaleTopology X)) :=
  let M := AddCommGrpCat.of (ULift.{u} ℤ)
  let adjU := sheafificationAdjunction (smallEtaleTopology U) AddCommGrpCat.{u}
  let adjX := sheafificationAdjunction (smallEtaleTopology X) AddCommGrpCat.{u}
  (adjU.homEquiv ((Functor.const _).obj M)
      ((etaleRestrictionSheaf ι AddCommGrpCat.{u}).obj
        (constantIntegerSheaf (smallEtaleTopology X)))).symm
    ((Functor.constCompWhiskeringLeftIso ((smallEtaleSite U)ᵒᵖ)
          (C := AddCommGrpCat.{u}) (etaleRestriction ι).op).inv.app M ≫
      Functor.whiskerLeft (etaleRestriction ι).op
        (adjX.unit.app ((Functor.const _).obj M)))

/-- `cohomologyIntegerPullbackHom` is the sheafification adjunct of the constant-presheaf
comparison along étale restriction. -/
theorem cohomologyIntegerPullbackHom_spec {X U : AlgebraicSpace S}
    (ι : U ⟶ X) [IsOpenImmersion ι] :
    (sheafificationAdjunction (smallEtaleTopology U) AddCommGrpCat.{u}).homEquiv
        ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
        ((etaleRestrictionSheaf ι AddCommGrpCat.{u}).obj (constantIntegerSheaf (smallEtaleTopology X)))
        (cohomologyIntegerPullbackHom ι) =
      (Functor.constCompWhiskeringLeftIso ((smallEtaleSite U)ᵒᵖ)
            (C := AddCommGrpCat.{u}) (etaleRestriction ι).op).inv.app
          (AddCommGrpCat.of (ULift.{u} ℤ)) ≫
        Functor.whiskerLeft (etaleRestriction ι).op
          ((sheafificationAdjunction (smallEtaleTopology X) AddCommGrpCat.{u}).unit.app
            ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) :=
  sorry

/-- The trace `Tr_ι : ι_! ℤ̲_U ⟶ ℤ̲_X`, adjunct of `cohomologyIntegerPullbackHom`. -/
noncomputable def cohomologyTrace {X U : AlgebraicSpace S}
    (ι : U ⟶ X) [IsOpenImmersion ι] :
    (etaleExtensionByZero ι AddCommGrpCat.{u}).obj (constantIntegerSheaf (smallEtaleTopology U)) ⟶
      constantIntegerSheaf (smallEtaleTopology X) :=
  ((etaleExtensionByZero_adjunction ι AddCommGrpCat.{u}).homEquiv
      (constantIntegerSheaf (smallEtaleTopology U)) (constantIntegerSheaf (smallEtaleTopology X))).symm
    (cohomologyIntegerPullbackHom ι)

/-- The trace is the adjunct of `cohomologyIntegerPullbackHom`. -/
theorem cohomologyTrace_spec {X U : AlgebraicSpace S}
    (ι : U ⟶ X) [IsOpenImmersion ι] :
    (etaleExtensionByZero_adjunction ι AddCommGrpCat.{u}).homEquiv
        (constantIntegerSheaf (smallEtaleTopology U)) (constantIntegerSheaf (smallEtaleTopology X)) (cohomologyTrace ι) =
      cohomologyIntegerPullbackHom ι :=
  sorry

/-- The underlying abelian sheaf of étale module restriction along an open immersion agrees
with sheaf restriction along `restrictPostcompose`. -/
noncomputable def toSheafRestrictPostcomposeIso {X U : AlgebraicSpace S}
    (ι : U ⟶ X) [IsOpenImmersion ι] (F : X.Modules) :
    (SheafOfModules.toSheaf (structureSheaf U)).obj (Modules.restrict F ι) ≅
      ((Modules.restrictPostcompose ι).sheafPushforwardContinuous AddCommGrpCat.{u}
        (smallEtaleTopology U) (smallEtaleTopology X)).obj
        ((SheafOfModules.toSheaf (structureSheaf X)).obj F) :=
  Iso.refl _

/-- `toSheafRestrictPostcomposeIso` is the identity comparison of underlying abelian sheaves. -/
theorem toSheafRestrictPostcomposeIso_hom {X U : AlgebraicSpace S}
    (ι : U ⟶ X) [IsOpenImmersion ι] (F : X.Modules) :
    toSheafRestrictPostcomposeIso ι F = Iso.refl _ :=
  rfl

/-- The underlying abelian sheaf of étale module restriction along an open immersion is
étale sheaf restriction of `toSheaf F`. -/
noncomputable def toSheafRestrictIso {X U : AlgebraicSpace S}
    (ι : U ⟶ X) [IsOpenImmersion ι] (F : X.Modules) :
    (SheafOfModules.toSheaf (structureSheaf U)).obj (Modules.restrict F ι) ≅
      (etaleRestrictionSheaf ι AddCommGrpCat.{u}).obj
        ((SheafOfModules.toSheaf (structureSheaf X)).obj F) :=
  toSheafRestrictPostcomposeIso ι F ≪≫
    (Functor.sheafPushforwardContinuousIso (Modules.restrictPostcomposeIso ι)
        AddCommGrpCat.{u} (smallEtaleTopology U) (smallEtaleTopology X)).app
      ((SheafOfModules.toSheaf (structureSheaf X)).obj F)

/-- `toSheafRestrictIso` is the `restrictPostcompose` identification followed by the
postcomposition iso from `restrictPostcompose` to `etaleRestriction`. -/
theorem toSheafRestrictIso_hom {X U : AlgebraicSpace S}
    (ι : U ⟶ X) [IsOpenImmersion ι] (F : X.Modules) :
    (toSheafRestrictIso ι F).hom =
      (toSheafRestrictPostcomposeIso ι F ≪≫
          (Functor.sheafPushforwardContinuousIso (Modules.restrictPostcomposeIso ι)
              AddCommGrpCat.{u} (smallEtaleTopology U) (smallEtaleTopology X)).app
            ((SheafOfModules.toSheaf (structureSheaf X)).obj F)).hom :=
  rfl

/-- Restriction of abelian-sheaf cohomology along an open immersion, induced by the
extension-by-zero trace and its adjunction unit. -/
noncomputable def sheafCohomologyRestrict {X U : AlgebraicSpace S}
    (ι : U ⟶ X) [IsOpenImmersion ι] (q : ℕ)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasSheafify (smallEtaleTopology U) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf (smallEtaleTopology U) AddCommGrpCat.{u})]
    [(etaleRestrictionSheaf ι AddCommGrpCat.{u}).Additive]
    [PreservesFiniteLimits (etaleRestrictionSheaf ι AddCommGrpCat.{u})]
    [PreservesFiniteColimits (etaleRestrictionSheaf ι AddCommGrpCat.{u})] :
    Sheaf.functorH (smallEtaleTopology X) q ⟶
      etaleRestrictionSheaf ι AddCommGrpCat.{u} ⋙
        Sheaf.functorH (smallEtaleTopology U) q where
  app G :=
    AddCommGrpCat.ofHom
      (((Ext.mk₀ ((etaleExtensionByZero_adjunction ι AddCommGrpCat.{u}).unit.app
                (constantIntegerSheaf (smallEtaleTopology U)))).precomp
            ((etaleRestrictionSheaf ι AddCommGrpCat.{u}).obj G)
            (zero_add q)).comp
        (((etaleRestrictionSheaf ι AddCommGrpCat.{u}).mapExtAddHom
              ((etaleExtensionByZero ι AddCommGrpCat.{u}).obj
                (constantIntegerSheaf (smallEtaleTopology U))) G q).comp
          ((Ext.mk₀ (cohomologyTrace ι)).precomp G (zero_add q))))
  naturality := by sorry

/-- Restriction `H^q(X, F) ⟶ H^q(U, F|_U)` along an open immersion, as Ext-precomposition
with the étale trace, transport along étale restriction, and `toSheafRestrictIso`. -/
noncomputable def cohomologyRestrict {X U : AlgebraicSpace S}
    (ι : U ⟶ X) [IsOpenImmersion ι] (F : X.Modules) (q : ℕ)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasSheafify (smallEtaleTopology U) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf (smallEtaleTopology U) AddCommGrpCat.{u})]
    [(etaleRestrictionSheaf ι AddCommGrpCat.{u}).Additive]
    [PreservesFiniteLimits (etaleRestrictionSheaf ι AddCommGrpCat.{u})]
    [PreservesFiniteColimits (etaleRestrictionSheaf ι AddCommGrpCat.{u})] :
    cohomology X F q ⟶ cohomology U (Modules.restrict F ι) q :=
  (sheafCohomologyRestrict ι q).app
      ((SheafOfModules.toSheaf (structureSheaf X)).obj F) ≫
    (Sheaf.functorH (smallEtaleTopology U) q).map (toSheafRestrictIso ι F).inv

/-- `cohomologyRestrict` is Ext-precomposition with the trace, followed by étale restriction
and `toSheafRestrictIso`. -/
theorem cohomologyRestrict_eq {X U : AlgebraicSpace S}
    (ι : U ⟶ X) [IsOpenImmersion ι] (F : X.Modules) (q : ℕ)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasSheafify (smallEtaleTopology U) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf (smallEtaleTopology U) AddCommGrpCat.{u})]
    [(etaleRestrictionSheaf ι AddCommGrpCat.{u}).Additive]
    [PreservesFiniteLimits (etaleRestrictionSheaf ι AddCommGrpCat.{u})]
    [PreservesFiniteColimits (etaleRestrictionSheaf ι AddCommGrpCat.{u})] :
    cohomologyRestrict ι F q =
      AddCommGrpCat.ofHom
        (((Ext.mk₀ (toSheafRestrictIso ι F).inv).postcomp
              (constantIntegerSheaf (smallEtaleTopology U)) (add_zero q)).comp
          (((Ext.mk₀ ((etaleExtensionByZero_adjunction ι AddCommGrpCat.{u}).unit.app
                    (constantIntegerSheaf (smallEtaleTopology U)))).precomp
                ((etaleRestrictionSheaf ι AddCommGrpCat.{u}).obj
                  ((SheafOfModules.toSheaf (structureSheaf X)).obj F))
                (zero_add q)).comp
            (((etaleRestrictionSheaf ι AddCommGrpCat.{u}).mapExtAddHom
                  ((etaleExtensionByZero ι AddCommGrpCat.{u}).obj (constantIntegerSheaf (smallEtaleTopology U)))
                  ((SheafOfModules.toSheaf (structureSheaf X)).obj F) q).comp
              ((Ext.mk₀ (cohomologyTrace ι)).precomp
                ((SheafOfModules.toSheaf (structureSheaf X)).obj F) (zero_add q))))) :=
  rfl

/-- Restriction along the identity open immersion is the identity on cohomology. -/
theorem cohomologyRestrict_id {X : AlgebraicSpace S} (F : X.Modules) (q : ℕ)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [(etaleRestrictionSheaf (𝟙 X) AddCommGrpCat.{u}).Additive]
    [PreservesFiniteLimits (etaleRestrictionSheaf (𝟙 X) AddCommGrpCat.{u})]
    [PreservesFiniteColimits (etaleRestrictionSheaf (𝟙 X) AddCommGrpCat.{u})] :
    cohomologyRestrict (𝟙 X) F q = 𝟙 (cohomology X F q) :=
  sorry

/-- Restriction in integer degrees, extended by the zero morphism in negative degrees. -/
noncomputable def cohomologyRestrictInt {X U : AlgebraicSpace S}
    (ι : U ⟶ X) [IsOpenImmersion ι] (F : X.Modules)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasSheafify (smallEtaleTopology U) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf (smallEtaleTopology U) AddCommGrpCat.{u})]
    [(etaleRestrictionSheaf ι AddCommGrpCat.{u}).Additive]
    [PreservesFiniteLimits (etaleRestrictionSheaf ι AddCommGrpCat.{u})]
    [PreservesFiniteColimits (etaleRestrictionSheaf ι AddCommGrpCat.{u})] (q : ℤ) :
    cohomologyInt X F q ⟶ cohomologyInt U (Modules.restrict F ι) q :=
  match q with
  | .ofNat n => cohomologyRestrict ι F n
  | .negSucc _ => 0

/-- Integer restriction agrees with ordinary restriction in nonnegative degrees. -/
@[simp] theorem cohomologyRestrictInt_ofNat {X U : AlgebraicSpace S}
    (ι : U ⟶ X) [IsOpenImmersion ι] (F : X.Modules)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasSheafify (smallEtaleTopology U) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf (smallEtaleTopology U) AddCommGrpCat.{u})]
    [(etaleRestrictionSheaf ι AddCommGrpCat.{u}).Additive]
    [PreservesFiniteLimits (etaleRestrictionSheaf ι AddCommGrpCat.{u})]
    [PreservesFiniteColimits (etaleRestrictionSheaf ι AddCommGrpCat.{u})] (n : ℕ) :
    cohomologyRestrictInt ι F (Int.ofNat n) = cohomologyRestrict ι F n := rfl

end AlgebraicGeometry.AlgebraicSpace
