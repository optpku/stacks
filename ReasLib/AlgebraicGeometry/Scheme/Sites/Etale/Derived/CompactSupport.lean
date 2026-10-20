module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.FixedInterior
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Coefficients

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

section LowerShriek

variable {Y : Scheme.{u}} (X : Over Y) {Λ : Type u} [Ring Λ]
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable (P : Compactification.Of Y X)
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      P.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]

/-- The derived lower shriek `Rf_!` of a separated finite-type morphism with
quasi-compact quasi-separated target, realized as `R f̄_* ∘ j_!` from an
explicit compactification `j : X.left ⟶ X̄` over `Y`. -/
def etaleDerivedLowerShriek :
    DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  (etaleExtensionByZero (Compactification.Of.ι P)
      (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
    etaleDerivedPushforward P.obj.right.hom

/-- Evaluating `Rf_!` applies extension by zero along the interior immersion
and then derived pushforward along the structure map of the compactification. -/
theorem etaleDerivedLowerShriek_obj (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (etaleDerivedLowerShriek X P).obj K =
      (etaleDerivedPushforward P.obj.right.hom).obj
        ((etaleExtensionByZero (Compactification.Of.ι P)
            (ModuleCat.{u} Λ)).mapDerivedCategory.obj K) := sorry

end LowerShriek

section CompactSupport

variable {k : Type u} [Field k] {Λ : Type u} [CommRing Λ]
variable {X : SchemeOverField k}
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable (P : Compactification.Of (Spec (CommRingCat.of k)) X)
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify (Spec (CommRingCat.of k)).smallEtaleTopology
  (ModuleCat.{u} Λ)]
variable [∀ U : (Spec (CommRingCat.of k)).Etale,
  HasWeakSheafify ((Spec (CommRingCat.of k)).smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) (Spec (CommRingCat.of k)).smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (Spec (CommRingCat.of k)).smallEtaleTopology
      P.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [HasDerivedCategory (ModuleCat.{u} Λ)]
variable [((sheafSections (Spec (CommRingCat.of k)).smallEtaleTopology
    (ModuleCat.{u} Λ)).obj
    (op (globalEtale (Spec (CommRingCat.of k))))).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((sheafSections (Spec (CommRingCat.of k)).smallEtaleTopology
        (ModuleCat.{u} Λ)).obj
      (op (globalEtale (Spec (CommRingCat.of k))))))
  (HomologicalComplex.quasiIso
    (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [CompactSpace (Spec (CommRingCat.of k))]
variable [QuasiSeparatedSpace (Spec (CommRingCat.of k))]

/-- The compactification model for derived sections with compact support,
obtained by composing derived lower shriek with derived sections on `Spec k`.
This functor is defined on the entire derived category for the chosen compactification. -/
def etaleDerivedGammaCompactSupport :
    DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (ModuleCat.{u} Λ) :=
  etaleDerivedLowerShriek X P ⋙
    etaleDerivedGamma (Spec (CommRingCat.of k)) Λ

/-- The compactification model evaluates as derived sections of derived lower shriek. -/
theorem etaleDerivedGammaCompactSupport_obj (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (etaleDerivedGammaCompactSupport P).obj K =
      (etaleDerivedGamma (Spec (CommRingCat.of k)) Λ).obj
        ((etaleDerivedLowerShriek X P).obj K) := sorry

/-- Degree-`i` homology of the compactification model for derived sections
with compact support, defined on the entire derived category. -/
def etaleDerivedCohomologyCompactSupport (i : ℤ) (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    ModuleCat.{u} Λ :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} Λ) i).obj
    ((etaleDerivedGammaCompactSupport P).obj K)

/-- Cohomology of the compactification model is homology of its derived sections. -/
theorem etaleDerivedCohomologyCompactSupport_eq
    (i : ℤ) (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    etaleDerivedCohomologyCompactSupport P i K =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} Λ) i).obj
        ((etaleDerivedGammaCompactSupport P).obj K) := sorry

namespace Derived

variable [X.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

/-- Derived sections with compact support on bounded-below torsion-cohomology
objects, or on all objects when the coefficient ring is torsion, computed using
an explicit compactification. -/
def compactSupport :
    (compactSupportAdmissible X.left Λ).FullSubcategory ⥤
      DerivedCategory (ModuleCat.{u} Λ) :=
  (compactSupportAdmissible X.left Λ).ι ⋙ etaleDerivedGammaCompactSupport P

/-- Derived sections with compact support evaluate as derived sections on
`Spec k` of the compactification realization of derived lower shriek. -/
theorem compactSupport_obj
    (K : (compactSupportAdmissible X.left Λ).FullSubcategory) :
    (compactSupport P).obj K =
      (etaleDerivedGamma (Spec (CommRingCat.of k)) Λ).obj
        ((etaleDerivedLowerShriek X P).obj K.obj) := sorry

/-- Integer-degree compactly supported cohomology is homology of derived
sections with compact support on the admissible full subcategory. -/
def cohomologyCompactSupport (i : ℤ)
    (K : (compactSupportAdmissible X.left Λ).FullSubcategory) : ModuleCat.{u} Λ :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} Λ) i).obj ((compactSupport P).obj K)

/-- Compactly supported cohomology is degree-`i` homology of derived sections
with compact support. -/
theorem cohomologyCompactSupport_eq (i : ℤ)
    (K : (compactSupportAdmissible X.left Λ).FullSubcategory) :
    cohomologyCompactSupport P i K =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} Λ) i).obj
        ((compactSupport P).obj K) := sorry

end Derived

end CompactSupport

end AlgebraicGeometry.Scheme.Etale

end
