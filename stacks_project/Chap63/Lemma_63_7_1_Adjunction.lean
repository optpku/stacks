module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.CategoryTheory.Adjunction.Derived.Unbounded
public import stacks_project.Chap59.Definition_59_77_1
public import stacks_project.Chap63.Lemma_63_6_1_Module

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
  [LocallyOfFiniteType f]
variable (Λ : Type u) [CommRing Λ]
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

/-- The sheaf-level upper shriek on étale sheaves of `Λ`-modules is additive. -/
instance upperShriekModule_additive [LocallyOfFiniteType f] :
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
def lowerShriekModuleDerived : EtaleDerived X Λ ⥤ EtaleDerived Y Λ :=
  have := ‹LocallyOfFiniteType f›
  (lowerShriekModule f Λ).mapDerivedCategory

/-- Derived compact-support direct image is `mapDerivedCategory` of
`lowerShriekModule`. -/
theorem lowerShriekModuleDerived_def :
    lowerShriekModuleDerived f Λ = (lowerShriekModule f Λ).mapDerivedCategory :=
  sorry

/-- Evaluating derived compact-support direct image on an object of
`D(X_étale, Λ)`. -/
theorem lowerShriekModuleDerived_obj (K : EtaleDerived X Λ) :
    (lowerShriekModuleDerived f Λ).obj K =
      (lowerShriekModule f Λ).mapDerivedCategory.obj K :=
  sorry

variable [IsGrothendieckAbelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Derived upper shriek `Rf^!` on `D(Y_étale, Λ)`, the K-injective total right
derived functor of `upperShriekModule`. -/
def upperShriekModuleDerived : EtaleDerived Y Λ ⥤ EtaleDerived X Λ :=
  have := ‹LocallyOfFiniteType f›
  Adjunction.Derived.KInjective.right (upperShriekModule f Λ)

/-- Derived upper shriek is the K-injective right-derived functor of
`upperShriekModule`. -/
theorem upperShriekModuleDerived_def :
    upperShriekModuleDerived f Λ =
      Adjunction.Derived.KInjective.right (upperShriekModule f Λ) :=
  sorry

/-- Evaluating derived upper shriek on an object of `D(Y_étale, Λ)`. -/
theorem upperShriekModuleDerived_obj (K : EtaleDerived Y Λ) :
    (upperShriekModuleDerived f Λ).obj K =
      (Adjunction.Derived.KInjective.right (upperShriekModule f Λ)).obj K :=
  sorry

/-- The unbounded derived adjunction `f_! ⊣ Rf^!` induced by the sheaf-level
module adjunction `lowerShriekModuleAdjunction`. -/
def lowerShriekModuleDerivedAdjunction :
    lowerShriekModuleDerived f Λ ⊣ upperShriekModuleDerived f Λ :=
  have := ‹LocallyOfFiniteType f›
  Adjunction.Derived.KInjective.adjunction
    (ExactFunctor.of (lowerShriekModule f Λ)) (upperShriekModule f Λ)
    (lowerShriekModuleAdjunction f Λ)

/-- The hom-equivalence of the derived compact-support adjunction. -/
def lowerShriekModuleDerivedAdjunction_homEquiv
    (L : EtaleDerived X Λ) (K : EtaleDerived Y Λ) :
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
  sorry

end AlgebraicGeometry.Scheme.Etale

end
