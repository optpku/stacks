module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.CategoryTheory.Adjunction.Derived.Unbounded
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.UpperShriek.LocallyQuasiFinite.Module

/-!
# Derived shriek adjunction for locally quasi-finite morphisms

Exact compact-support `f_!` on étale sheaves of `Λ`-modules induces a functor
on unbounded derived categories, and K-injective resolutions of sheaves on
`Y_étale` supply the total right derived functor `Rf^!`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
variable (Λ : Type u) [Ring Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]

/-- Compact-support direct image on étale sheaves of `Λ`-modules is additive. -/
instance lowerShriekModule_additive [LocallyOfFiniteType f] :
    (lowerShriekModule f Λ).Additive :=
  sorry

/-- Compact-support direct image on étale sheaves of `Λ`-modules preserves finite
limits. -/
instance lowerShriekModule_preservesFiniteLimits [LocallyOfFiniteType f] :
    PreservesFiniteLimits (lowerShriekModule f Λ) :=
  sorry

/-- Compact-support direct image on étale sheaves of `Λ`-modules preserves finite
colimits. -/
instance lowerShriekModule_preservesFiniteColimits [LocallyOfFiniteType f] :
    PreservesFiniteColimits (lowerShriekModule f Λ) :=
  sorry

variable [LocallyOfFiniteType f]

/-- The sheaf-level upper shriek on étale sheaves of `Λ`-modules is additive. -/
instance upperShriekModule_additive :
    (upperShriekModule f Λ).Additive :=
  sorry

variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Derived compact-support direct image `f_!` on `D(X_étale, Λ)`, induced by the
exact sheaf-level functor `lowerShriekModule`. Exactness of `f_!` means this is
also `Lf_!`. -/
def lowerShriekModuleDerived :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  (lowerShriekModule f Λ).mapDerivedCategory

/-- Derived compact-support direct image is `mapDerivedCategory` of
`lowerShriekModule`. -/
theorem lowerShriekModuleDerived_def :
    lowerShriekModuleDerived f Λ = (lowerShriekModule f Λ).mapDerivedCategory :=
  rfl

/-- Evaluating derived compact-support direct image on an object of
`D(X_étale, Λ)`. -/
theorem lowerShriekModuleDerived_obj
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (lowerShriekModuleDerived f Λ).obj K =
      (lowerShriekModule f Λ).mapDerivedCategory.obj K :=
  rfl

variable [IsGrothendieckAbelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Derived upper shriek `Rf^!` on `D(Y_étale, Λ)`, the K-injective total right
derived functor of `upperShriekModule`. -/
def upperShriekModuleDerived :
    DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  Adjunction.Derived.KInjective.right (upperShriekModule f Λ)

/-- Derived upper shriek is the K-injective right-derived functor of
`upperShriekModule`. -/
theorem upperShriekModuleDerived_def :
    upperShriekModuleDerived f Λ =
      Adjunction.Derived.KInjective.right (upperShriekModule f Λ) :=
  rfl

/-- Evaluating derived upper shriek on an object of `D(Y_étale, Λ)`. -/
theorem upperShriekModuleDerived_obj
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (upperShriekModuleDerived f Λ).obj K =
      (Adjunction.Derived.KInjective.right (upperShriekModule f Λ)).obj K :=
  rfl

/-- The unbounded derived adjunction `f_! ⊣ Rf^!` induced by the sheaf-level
module adjunction `lowerShriekModuleAdjunction`. -/
def lowerShriekModuleDerivedAdjunction :
    lowerShriekModuleDerived f Λ ⊣ upperShriekModuleDerived f Λ :=
  Adjunction.Derived.KInjective.adjunction
    (ExactFunctor.of (lowerShriekModule f Λ)) (upperShriekModule f Λ)
    (lowerShriekModuleAdjunction f Λ)

/-- The hom-equivalence of the derived compact-support adjunction. -/
def lowerShriekModuleDerivedAdjunction_homEquiv
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) :
    ((lowerShriekModuleDerived f Λ).obj L ⟶ K) ≃
      (L ⟶ (upperShriekModuleDerived f Λ).obj K) :=
  (lowerShriekModuleDerivedAdjunction f Λ).homEquiv L K

/-- The derived compact-support adjunction is the K-injective derived
adjunction of `lowerShriekModuleAdjunction`. -/
theorem lowerShriekModuleDerivedAdjunction_def :
    lowerShriekModuleDerivedAdjunction f Λ =
      Adjunction.Derived.KInjective.adjunction
        (ExactFunctor.of (lowerShriekModule f Λ)) (upperShriekModule f Λ)
        (lowerShriekModuleAdjunction f Λ) :=
  rfl

end AlgebraicGeometry.Scheme.Etale

end
