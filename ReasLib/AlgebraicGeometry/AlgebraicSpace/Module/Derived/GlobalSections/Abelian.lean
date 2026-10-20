/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Basic
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Sections
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.GlobalSections

/-!
# Abelian-valued derived global sections of modules on algebraic spaces

Forgetting the `Γ(X, 𝒪_X)`-module structure puts `RΓ(X, -)` in the single category
`D(Ab.{u})`, so derived global sections on different algebraic spaces can be compared.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Global sections of an `𝒪_X`-module, as an abelian group. -/
noncomputable def moduleGlobalSectionsAb {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X.Modules ⥤ AddCommGrpCat.{u} :=
  moduleGlobalSectionsFunctor X ⋙
    forget₂ (ModuleCat.{u} (globalSectionsRing X)) AddCommGrpCat.{u}

/-- On objects, `moduleGlobalSectionsAb` is `forget₂` of `moduleGlobalSectionsFunctor`. -/
theorem moduleGlobalSectionsAb_obj {S : Scheme.{u}} (X : AlgebraicSpace S) (F : X.Modules) :
    (moduleGlobalSectionsAb X).obj F =
      (forget₂ (ModuleCat.{u} (globalSectionsRing X)) AddCommGrpCat.{u}).obj
        ((moduleGlobalSectionsFunctor X).obj F) :=
  rfl

/-- Abelian-valued global sections is an additive functor. -/
instance moduleGlobalSectionsAb.additive {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (moduleGlobalSectionsAb X).Additive :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The unbounded derived global-sections functor `RΓ(X, -) : D(𝒪_X) ⥤ D(Ab.{u})`. -/
noncomputable abbrev moduleDerivedGlobalSectionsAb {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ModuleDerived X ⥤ DerivedCategory AddCommGrpCat.{u} :=
  Functor.RightDerived.KInjective.functor.{u} (moduleGlobalSectionsAb X)

/-- Abelian-valued derived global sections is the K-injective right derived functor of
`moduleGlobalSectionsAb`. -/
theorem moduleDerivedGlobalSectionsAb_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    moduleDerivedGlobalSectionsAb X =
      Functor.RightDerived.KInjective.functor.{u} (moduleGlobalSectionsAb X) :=
  rfl

namespace moduleDerivedGlobalSectionsAb

/-- The cochain-level comparison unit for abelian-valued derived global sections. -/
noncomputable abbrev unit {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (moduleGlobalSectionsAb X).mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q :
          CochainComplex AddCommGrpCat.{u} ℤ ⥤ DerivedCategory AddCommGrpCat.{u}) ⟶
      (DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ ModuleDerived X) ⋙
        moduleDerivedGlobalSectionsAb X :=
  Functor.RightDerived.KInjective.unit.{u} (moduleGlobalSectionsAb X)

/-- Abelian-valued derived global sections satisfies the universal property of a
right-derived functor. -/
instance isRightDerived {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (moduleDerivedGlobalSectionsAb X).IsRightDerivedFunctor (unit X)
      (HomologicalComplex.quasiIso (Modules X) (up ℤ)) :=
  Functor.RightDerived.KInjective.isRightDerived (moduleGlobalSectionsAb X)

/-- The homotopy-to-derived functor of abelian-valued global sections is defined
at every complex. -/
instance everywhereDefined {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Functor.RightDerived.EverywhereDefined
      (Functor.Homotopy.toDerived (moduleGlobalSectionsAb X))
      (HomotopyCategory.quasiIso X.Modules (up ℤ)) :=
  sorry

/-- Abelian-valued derived global sections commutes with the integer shift. -/
noncomputable instance commShift {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (moduleDerivedGlobalSectionsAb X).CommShift ℤ :=
  inferInstance

/-- Abelian-valued derived global sections is additive. -/
instance additive {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (moduleDerivedGlobalSectionsAb X).Additive :=
  sorry

end moduleDerivedGlobalSectionsAb

/-- Degree-`n` hypercohomology `H^n(X, E)` as an abelian group. -/
noncomputable abbrev cohomologyAb {S : Scheme.{u}} (X : AlgebraicSpace S)
    (E : ModuleDerived X) (n : ℤ) : AddCommGrpCat.{u} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
    ((moduleDerivedGlobalSectionsAb X).obj E)

/-- A morphism in `D(𝒪_X)` induces a map on abelian-valued hypercohomology. -/
def cohomologyAb_map {S : Scheme.{u}} {X : AlgebraicSpace S}
    {E E' : ModuleDerived X} (φ : E ⟶ E') (n : ℤ) :
    cohomologyAb X E n ⟶ cohomologyAb X E' n :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
    ((moduleDerivedGlobalSectionsAb X).map φ)

/-- `cohomologyAb_map` is homology of abelian-valued derived global sections. -/
theorem cohomologyAb_map_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {E E' : ModuleDerived X} (φ : E ⟶ E') (n : ℤ) :
    cohomologyAb_map φ n =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
        ((moduleDerivedGlobalSectionsAb X).map φ) :=
  rfl

/-- Cochain-level unit of `A`-linear `RΓ` followed by `forget₂` on derived categories. -/
def moduleDerivedGlobalSectionsAbForgetUnit {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (moduleGlobalSectionsAb X).mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q :
          CochainComplex AddCommGrpCat.{u} ℤ ⥤ DerivedCategory AddCommGrpCat.{u}) ⟶
      (DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ ModuleDerived X) ⋙
        (moduleDerivedGlobalSections X ⋙
          ModuleCat.forgetDerived (globalSectionsRing X)) :=
  whiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (moduleGlobalSectionsAb X)) (up ℤ)).inv
      DerivedCategory.Q ≫
    (associator
      ((moduleGlobalSectionsFunctor X).mapHomologicalComplex (up ℤ))
      ((forget₂ (ModuleCat.{u} (globalSectionsRing X))
          AddCommGrpCat.{u}).mapHomologicalComplex (up ℤ))
      (DerivedCategory.Q :
        CochainComplex AddCommGrpCat.{u} ℤ ⥤ DerivedCategory AddCommGrpCat.{u})).hom ≫
    whiskerLeft ((moduleGlobalSectionsFunctor X).mapHomologicalComplex (up ℤ))
      ((forget₂ (ModuleCat.{u} (globalSectionsRing X))
          AddCommGrpCat.{u}).mapDerivedCategoryFactors.inv) ≫
    (associator
      ((moduleGlobalSectionsFunctor X).mapHomologicalComplex (up ℤ))
      (DerivedCategory.Q :
        CochainComplex (ModuleCat.{u} (globalSectionsRing X)) ℤ ⥤
          DerivedCategory (ModuleCat.{u} (globalSectionsRing X)))
      (ModuleCat.forgetDerived (globalSectionsRing X))).inv ≫
    whiskerRight (moduleDerivedGlobalSections.unit X)
      (ModuleCat.forgetDerived (globalSectionsRing X)) ≫
    (associator
      (DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ ModuleDerived X)
      (moduleDerivedGlobalSections X)
      (ModuleCat.forgetDerived (globalSectionsRing X))).hom

/-- Comparison of abelian-valued `RΓ` with `A`-linear `RΓ` followed by `forget₂`. -/
def moduleDerivedGlobalSectionsAbComparison {S : Scheme.{u}} (X : AlgebraicSpace S) :
    moduleDerivedGlobalSectionsAb X ⟶
      moduleDerivedGlobalSections X ⋙
        ModuleCat.forgetDerived (globalSectionsRing X) :=
  (moduleDerivedGlobalSectionsAb X).rightDerivedDesc
    (moduleDerivedGlobalSectionsAb.unit X)
    (HomologicalComplex.quasiIso (Modules X) (up ℤ))
    (moduleDerivedGlobalSections X ⋙
      ModuleCat.forgetDerived (globalSectionsRing X))
    (moduleDerivedGlobalSectionsAbForgetUnit X)

/-- The comparison of abelian-valued `RΓ` with `A`-linear `RΓ` then `forget₂` is an
isomorphism. -/
instance isIso_moduleDerivedGlobalSectionsAbComparison {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    IsIso (moduleDerivedGlobalSectionsAbComparison X) :=
  sorry

/-- Identification of abelian-valued `RΓ` with `A`-linear `RΓ` followed by `forget₂`. -/
def moduleDerivedGlobalSectionsAbIso {S : Scheme.{u}} (X : AlgebraicSpace S) :
    moduleDerivedGlobalSectionsAb X ≅
      moduleDerivedGlobalSections X ⋙
        ModuleCat.forgetDerived (globalSectionsRing X) :=
  asIso (moduleDerivedGlobalSectionsAbComparison X)

/-- The forward map of `moduleDerivedGlobalSectionsAbIso` is the named comparison. -/
theorem moduleDerivedGlobalSectionsAbIso_hom {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (moduleDerivedGlobalSectionsAbIso X).hom =
      moduleDerivedGlobalSectionsAbComparison X :=
  rfl

/-- Universe lift of abelian-valued global sections, matching the universe of
compatible sections. -/
abbrev moduleGlobalSectionsAbULift {S : Scheme.{u}} (X : AlgebraicSpace S) (F : X.Modules) :
    AddCommGrpCat.{u + 1} :=
  AddCommGrpCat.uliftFunctor.{u + 1, u}.obj ((moduleGlobalSectionsAb X).obj F)

/-- Evaluation of compatible sections at Spec A preserves zero and addition. -/
private theorem toSpecAGlobalSectionHom_laws {S : Scheme.{u}}
    (X : AlgebraicSpace S) (F : X.Modules) :
    let g : F.sections → moduleGlobalSectionsAbULift X F :=
      fun s ↦ ULift.up (toSpecAGlobalSection X F s)
    g 0 = 0 ∧ ∀ s t, g (s + t) = g s + g t :=
  sorry

/-- Spec-A evaluation of compatible sections, as an abelian-group homomorphism. -/
def toSpecAGlobalSectionHom {S : Scheme.{u}} (X : AlgebraicSpace S) (F : X.Modules) :
    AddCommGrpCat.of F.sections ⟶ moduleGlobalSectionsAbULift X F :=
  AddCommGrpCat.ofHom
    { toFun := fun s ↦ ULift.up (toSpecAGlobalSection X F s)
      map_zero' := by exact (toSpecAGlobalSectionHom_laws X F).1
      map_add' := by exact (toSpecAGlobalSectionHom_laws X F).2 }

/-- Spec-A evaluation of compatible sections is an isomorphism of abelian groups. -/
instance isIso_toSpecAGlobalSectionHom {S : Scheme.{u}} (X : AlgebraicSpace S)
    (F : X.Modules) :
    IsIso (toSpecAGlobalSectionHom X F) :=
  sorry

/-- Identification of compatible sections with the universe lift of abelian-valued
global sections. -/
def toSpecAGlobalSectionIso {S : Scheme.{u}} (X : AlgebraicSpace S) (F : X.Modules) :
    AddCommGrpCat.of F.sections ≅ moduleGlobalSectionsAbULift X F :=
  asIso (toSpecAGlobalSectionHom X F)

/-- The forward map of `toSpecAGlobalSectionIso` is `toSpecAGlobalSectionHom`. -/
theorem toSpecAGlobalSectionIso_hom {S : Scheme.{u}} (X : AlgebraicSpace S)
    (F : X.Modules) :
    (toSpecAGlobalSectionIso X F).hom = toSpecAGlobalSectionHom X F :=
  rfl

/-- Direct-image evaluation of compatible sections preserves zero and addition. -/
private theorem gammaPushforwardSectionHom_laws {S : Scheme.{u}}
    {W X : AlgebraicSpace S} (h : W ⟶ X) (F : W.Modules) :
    let g : F.sections → moduleGlobalSectionsAbULift X ((pushforward h).obj F) :=
      fun s ↦ ULift.up (toSpecAGlobalSection X ((pushforward h).obj F)
        (moduleDirectImageSection h F s))
    g 0 = 0 ∧ ∀ s t, g (s + t) = g s + g t :=
  sorry

/-- Direct image of a compatible section, followed by Spec-A evaluation on the target. -/
def gammaPushforwardSectionHom {S : Scheme.{u}} {W X : AlgebraicSpace S}
    (h : W ⟶ X) (F : W.Modules) :
    AddCommGrpCat.of F.sections ⟶
      moduleGlobalSectionsAbULift X ((pushforward h).obj F) :=
  AddCommGrpCat.ofHom
    { toFun := fun s ↦
        ULift.up
          (toSpecAGlobalSection X ((pushforward h).obj F)
            (moduleDirectImageSection h F s))
      map_zero' := by exact (gammaPushforwardSectionHom_laws h F).1
      map_add' := by exact (gammaPushforwardSectionHom_laws h F).2 }

/-- Direct image of sections followed by Spec-A evaluation is an isomorphism. -/
instance isIso_gammaPushforwardSectionHom {S : Scheme.{u}} {W X : AlgebraicSpace S}
    (h : W ⟶ X) (F : W.Modules) :
    IsIso (gammaPushforwardSectionHom h F) :=
  sorry

/-- Identification of compatible sections of `F` with the universe lift of abelian-valued
global sections of `h_* F`. -/
def gammaPushforwardSectionIso {S : Scheme.{u}} {W X : AlgebraicSpace S}
    (h : W ⟶ X) (F : W.Modules) :
    AddCommGrpCat.of F.sections ≅
      moduleGlobalSectionsAbULift X ((pushforward h).obj F) :=
  asIso (gammaPushforwardSectionHom h F)

/-- The forward map of `gammaPushforwardSectionIso` is `gammaPushforwardSectionHom`. -/
theorem gammaPushforwardSectionIso_hom {S : Scheme.{u}} {W X : AlgebraicSpace S}
    (h : W ⟶ X) (F : W.Modules) :
    (gammaPushforwardSectionIso h F).hom = gammaPushforwardSectionHom h F :=
  rfl

/-- Transporting direct-image evaluation to global sections preserves zero and addition. -/
private theorem gammaPushforwardForwardApp_laws {S : Scheme.{u}}
    {W X : AlgebraicSpace S} (h : W ⟶ X) (F : W.Modules) :
    let g : (moduleGlobalSectionsAb W).obj F →
        (moduleGlobalSectionsAb X).obj ((pushforward h).obj F) :=
      fun y ↦ ULift.down (gammaPushforwardSectionHom h F
        ((toSpecAGlobalSectionIso W F).inv (ULift.up y)))
    g 0 = 0 ∧ ∀ s t, g (s + t) = g s + g t :=
  sorry

/-- Direct-image evaluation transported along the Spec-A section isomorphism. -/
private def gammaPushforwardForwardApp {S : Scheme.{u}} {W X : AlgebraicSpace S}
    (h : W ⟶ X) (F : W.Modules) :
    (moduleGlobalSectionsAb W).obj F ⟶
      (moduleGlobalSectionsAb X).obj ((pushforward h).obj F) :=
  AddCommGrpCat.ofHom
    { toFun := fun y ↦
        ULift.down (gammaPushforwardSectionHom h F
          ((toSpecAGlobalSectionIso W F).inv (ULift.up y)))
      map_zero' := (gammaPushforwardForwardApp_laws h F).1
      map_add' := (gammaPushforwardForwardApp_laws h F).2 }

/-- Transported direct-image evaluation is natural in the module. -/
private theorem gammaPushforwardForwardApp_naturality {S : Scheme.{u}}
    {W X : AlgebraicSpace S} (h : W ⟶ X) {F G : W.Modules} (φ : F ⟶ G) :
    (moduleGlobalSectionsAb W).map φ ≫ gammaPushforwardForwardApp h G =
      gammaPushforwardForwardApp h F ≫ (pushforward h ⋙ moduleGlobalSectionsAb X).map φ :=
  sorry

/-- Forward underived comparison `Γ(W, -) ⟶ Γ(X, h_* -)`, obtained by transporting the
section-level direct-image evaluation along Spec-A evaluation. -/
@[no_expose] def gammaPushforwardForward {S : Scheme.{u}} {W X : AlgebraicSpace S} (h : W ⟶ X) :
    moduleGlobalSectionsAb W ⟶ pushforward h ⋙ moduleGlobalSectionsAb X where
  app F := gammaPushforwardForwardApp h F
  naturality := fun _ _ φ ↦ gammaPushforwardForwardApp_naturality h φ

/-- The forward comparison `Γ(W, -) ⟶ Γ(X, h_* -)` is an isomorphism. -/
instance isIso_gammaPushforwardForward {S : Scheme.{u}} {W X : AlgebraicSpace S}
    (h : W ⟶ X) :
    IsIso (gammaPushforwardForward h) :=
  sorry

/-- Underived identification `Γ(X, h_* -) ≅ Γ(W, -)`, inverse to the forward
section-level comparison. -/
def gammaPushforwardIso {S : Scheme.{u}} {W X : AlgebraicSpace S} (h : W ⟶ X) :
    pushforward h ⋙ moduleGlobalSectionsAb X ≅ moduleGlobalSectionsAb W :=
  (asIso (gammaPushforwardForward h)).symm

/-- Underived comparison `Γ(X, h_* -) ⟶ Γ(W, -)` of abelian-valued global sections. -/
def gammaPushforwardComparison {S : Scheme.{u}} {W X : AlgebraicSpace S} (h : W ⟶ X) :
    pushforward h ⋙ moduleGlobalSectionsAb X ⟶ moduleGlobalSectionsAb W :=
  (gammaPushforwardIso h).hom

/-- The forward map of `gammaPushforwardIso` is `gammaPushforwardComparison`. -/
theorem gammaPushforwardIso_hom {S : Scheme.{u}} {W X : AlgebraicSpace S} (h : W ⟶ X) :
    (gammaPushforwardIso h).hom = gammaPushforwardComparison h :=
  rfl

/-- The inverse of `gammaPushforwardIso` is the forward section-level comparison. -/
theorem gammaPushforwardIso_inv {S : Scheme.{u}} {W X : AlgebraicSpace S} (h : W ⟶ X) :
    (gammaPushforwardIso h).inv = gammaPushforwardForward h :=
  rfl

/-- Objectwise, `gammaPushforwardIso` is the component of `gammaPushforwardComparison`. -/
theorem gammaPushforwardIso_app {S : Scheme.{u}} {W X : AlgebraicSpace S}
    (h : W ⟶ X) (F : W.Modules) :
    (gammaPushforwardIso h).hom.app F = (gammaPushforwardComparison h).app F :=
  rfl

/-- Cochain-level iterated unit of `Rh_*` followed by abelian-valued `RΓ(X, -)`. -/
def derivedGammaPushforwardCompositeUnit {S : Scheme.{u}} {W X : AlgebraicSpace S}
    (h : W ⟶ X) :
    (pushforward h ⋙ moduleGlobalSectionsAb X).mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q :
          CochainComplex AddCommGrpCat.{u} ℤ ⥤ DerivedCategory AddCommGrpCat.{u}) ⟶
      (DerivedCategory.Q : CochainComplex (Modules W) ℤ ⥤ ModuleDerived W) ⋙
        (moduleDerivedPushforward h ⋙ moduleDerivedGlobalSectionsAb X) :=
  whiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (pushforward h ⋙ moduleGlobalSectionsAb X)) (up ℤ)).inv
      DerivedCategory.Q ≫
    (associator
      ((pushforward h).mapHomologicalComplex (up ℤ))
      ((moduleGlobalSectionsAb X).mapHomologicalComplex (up ℤ))
      (DerivedCategory.Q :
        CochainComplex AddCommGrpCat.{u} ℤ ⥤ DerivedCategory AddCommGrpCat.{u})).hom ≫
    whiskerLeft ((pushforward h).mapHomologicalComplex (up ℤ))
      (Functor.RightDerived.KInjective.unit.{u} (moduleGlobalSectionsAb X)) ≫
    (associator
      ((pushforward h).mapHomologicalComplex (up ℤ))
      (DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ ModuleDerived X)
      (moduleDerivedGlobalSectionsAb X)).inv ≫
    whiskerRight (Functor.RightDerived.KInjective.unit.{u} (pushforward h))
      (moduleDerivedGlobalSectionsAb X) ≫
    (associator
      (DerivedCategory.Q : CochainComplex (Modules W) ℤ ⥤ ModuleDerived W)
      (moduleDerivedPushforward h) (moduleDerivedGlobalSectionsAb X)).hom

/-- The composite `Rh_* ⋙ RΓ(X, -)` is a cochain-level right-derived model of
`Γ(X, h_* -)`. -/
instance derivedGammaPushforwardComposite_isRightDerived {S : Scheme.{u}}
    {W X : AlgebraicSpace S} (h : W ⟶ X) :
    (moduleDerivedPushforward h ⋙ moduleDerivedGlobalSectionsAb X).IsRightDerivedFunctor
      (derivedGammaPushforwardCompositeUnit h)
      (HomologicalComplex.quasiIso W.Modules (up ℤ)) :=
  sorry

/-- Canonical Leray map `RΓ(X, Rh_* F) ⟶ RΓ(W, F)` in `D(Ab.{u})`. -/
def derivedGammaPushforwardComparison {S : Scheme.{u}} {W X : AlgebraicSpace S}
    (h : W ⟶ X) [Etale h] :
    moduleDerivedPushforward h ⋙ moduleDerivedGlobalSectionsAb X ⟶
      moduleDerivedGlobalSectionsAb W :=
  (moduleDerivedPushforward h ⋙ moduleDerivedGlobalSectionsAb X).rightDerivedDesc
    (derivedGammaPushforwardCompositeUnit h)
    (HomologicalComplex.quasiIso W.Modules (up ℤ))
    (moduleDerivedGlobalSectionsAb W)
    (whiskerRight (NatTrans.mapHomologicalComplex (gammaPushforwardComparison h) (up ℤ))
        DerivedCategory.Q ≫
      Functor.RightDerived.KInjective.unit.{u} (moduleGlobalSectionsAb W))

/-- The Leray comparison `RΓ(X, Rh_* -) ⟶ RΓ(W, -)` is an isomorphism. -/
instance isIso_derivedGammaPushforwardComparison {S : Scheme.{u}} {W X : AlgebraicSpace S}
    (h : W ⟶ X) [Etale h] :
    IsIso (derivedGammaPushforwardComparison h) :=
  sorry

/-- Identification `RΓ(X, Rh_* F) ≅ RΓ(W, F)` of abelian-valued derived global sections. -/
def derivedGammaPushforwardIso {S : Scheme.{u}} {W X : AlgebraicSpace S}
    (h : W ⟶ X) [Etale h] :
    moduleDerivedPushforward h ⋙ moduleDerivedGlobalSectionsAb X ≅
      moduleDerivedGlobalSectionsAb W :=
  asIso (derivedGammaPushforwardComparison h)

/-- The forward map of `derivedGammaPushforwardIso` is `derivedGammaPushforwardComparison`. -/
theorem derivedGammaPushforwardIso_hom {S : Scheme.{u}} {W X : AlgebraicSpace S}
    (h : W ⟶ X) [Etale h] :
    (derivedGammaPushforwardIso h).hom = derivedGammaPushforwardComparison h :=
  rfl

/-- Objectwise, `derivedGammaPushforwardIso` is the component of the Leray comparison. -/
def derivedGammaPushforwardIso_app {S : Scheme.{u}} {W X : AlgebraicSpace S}
    (h : W ⟶ X) [Etale h] (F : ModuleDerived W) :
    (moduleDerivedGlobalSectionsAb X).obj ((moduleDerivedPushforward h).obj F) ≅
      (moduleDerivedGlobalSectionsAb W).obj F :=
  (derivedGammaPushforwardIso h).app F

end AlgebraicGeometry.AlgebraicSpace.Modules
