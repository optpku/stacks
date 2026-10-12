/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.ModulePullback
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Identity
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Derived

/-!
# Derived restriction along pro-étale base change

Restriction of derived objects of sheaves of `Λ`-modules is the derived functor
of `modulePullback` along `baseChange`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme.ProEt

variable {Y X : Scheme.{u}}

/-- Pro-étale base change presents a morphism of sites. -/
instance baseChange_isMorphismOfSites (f : Y ⟶ X) :
    IsMorphismOfSites (topology X) (topology Y) (baseChange f) :=
  sorry

/-- Inverse image of sheaves of `Λ`-modules along a scheme morphism. -/
def restrictSheaf (Λ : Type w) [Ring Λ] (f : Y ⟶ X)
    [∀ P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ, (baseChange f).op.HasLeftKanExtension P]
    [HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)] :
    Sheaf (topology X) (ModuleCat.{w} Λ) ⥤ Sheaf (topology Y) (ModuleCat.{w} Λ) :=
  modulePullback f

/-- `restrictSheaf` is `modulePullback`. -/
theorem restrictSheaf_def (Λ : Type w) [Ring Λ] (f : Y ⟶ X)
    [∀ P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ, (baseChange f).op.HasLeftKanExtension P]
    [HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)] :
    restrictSheaf Λ f = modulePullback f :=
  sorry

variable {Λ : Type w} [Ring Λ]
variable [Abelian (Sheaf (topology X) (ModuleCat.{w} Λ))]
variable [Abelian (Sheaf (topology Y) (ModuleCat.{w} Λ))]

section

/-- Inverse image of sheaves of `Λ`-modules along a scheme morphism is additive. -/
instance restrictSheaf_additive (f : Y ⟶ X)
    [∀ P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ, (baseChange f).op.HasLeftKanExtension P]
    [HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)] :
    (restrictSheaf Λ f).Additive :=
  sorry

/-- Inverse image of sheaves of `Λ`-modules along a scheme morphism preserves finite limits. -/
instance restrictSheaf_preservesFiniteLimits (f : Y ⟶ X)
    [∀ P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ, (baseChange f).op.HasLeftKanExtension P]
    [HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)] :
    PreservesFiniteLimits (restrictSheaf Λ f) :=
  sorry

/-- Inverse image of sheaves of `Λ`-modules along a scheme morphism preserves finite colimits. -/
instance restrictSheaf_preservesFiniteColimits (f : Y ⟶ X)
    [∀ P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ, (baseChange f).op.HasLeftKanExtension P]
    [HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)] :
    PreservesFiniteColimits (restrictSheaf Λ f) :=
  sorry

/-- Derived restriction of sheaves of `Λ`-modules along a scheme morphism, induced by
pro-étale base change. -/
def restrictDerived (f : Y ⟶ X)
    [∀ P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ, (baseChange f).op.HasLeftKanExtension P]
    [HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)]
    [HasDerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))]
    [HasDerivedCategory (Sheaf (topology Y) (ModuleCat.{w} Λ))] :
    DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ)) ⥤
      DerivedCategory (Sheaf (topology Y) (ModuleCat.{w} Λ)) :=
  (restrictSheaf Λ f).mapDerivedCategory

/-- `restrictDerived` is the derived functor of `restrictSheaf`. -/
theorem restrictDerived_def (f : Y ⟶ X)
    [∀ P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ, (baseChange f).op.HasLeftKanExtension P]
    [HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)]
    [HasDerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))]
    [HasDerivedCategory (Sheaf (topology Y) (ModuleCat.{w} Λ))] :
    restrictDerived f = (restrictSheaf Λ f).mapDerivedCategory :=
  sorry

/-- Derived restriction along the identity is isomorphic to the identity functor. -/
def restrictDerived_id
    [∀ P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ, (baseChange (𝟙 X)).op.HasLeftKanExtension P]
    [HasWeakSheafify (topology X) (ModuleCat.{w} Λ)]
    [HasDerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))] :
    restrictDerived (𝟙 X) ≅
      𝟭 (DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))) :=
  Functor.MapDerivedCategory.functorIso (F := restrictSheaf Λ (𝟙 X))
      (modulePullback_id (X := X) (Λ := Λ)) ≪≫
    ExactFunctor.MapDerivedCategory.idFunctorIso
      (Sheaf (topology X) (ModuleCat.{w} Λ))

/-- Derived restriction along a composite is isomorphic to the composite of the derived
restrictions. -/
def restrictDerived_comp {Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X)
    [Abelian (Sheaf (topology Z) (ModuleCat.{w} Λ))]
    [HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)]
    [HasWeakSheafify (topology Z) (ModuleCat.{w} Λ)]
    [HasDerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))]
    [HasDerivedCategory (Sheaf (topology Y) (ModuleCat.{w} Λ))]
    [HasDerivedCategory (Sheaf (topology Z) (ModuleCat.{w} Λ))]
    [∀ P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ, (baseChange f).op.HasLeftKanExtension P]
    [∀ P : Y.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ, (baseChange g).op.HasLeftKanExtension P]
    [∀ P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ, (baseChange (g ≫ f)).op.HasLeftKanExtension P] :
    (restrictDerived (g ≫ f) :
        DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ)) ⥤
          DerivedCategory (Sheaf (topology Z) (ModuleCat.{w} Λ))) ≅
      restrictDerived f ⋙ restrictDerived g :=
  Functor.MapDerivedCategory.functorIso
      (F := restrictSheaf Λ (g ≫ f)) (G := restrictSheaf Λ f ⋙ restrictSheaf Λ g)
      (modulePullback_comp g f) ≪≫
    ExactFunctor.MapDerivedCategory.compFunctorIso
      (ExactFunctor.of (restrictSheaf Λ f))
      (ExactFunctor.of (restrictSheaf Λ g))

end

end AlgebraicGeometry.Scheme.ProEt
