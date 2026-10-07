module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Sites.Abelian
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import stacks_project.Chap59.Theorem_59_51_3_Cohomology
public import stacks_project.Chap63.Definition_63_12_1_LowerShriek

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

section DerivedGamma

variable (X : Scheme.{u}) (Λ : Type u) [CommRing Λ]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (ModuleCat.{u} Λ)]
variable [((sheafSections X.smallEtaleTopology (ModuleCat.{u} Λ)).obj
    (op (globalEtale X))).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((sheafSections X.smallEtaleTopology (ModuleCat.{u} Λ)).obj
      (op (globalEtale X))))
  (HomologicalComplex.quasiIso
    (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]

/-- Derived global sections `RΓ(X, -)` on `D(X_étale, Λ)`, obtained as the
total right derived functor of small-étale module sections at `globalEtale X`. -/
def etaleDerivedGamma :
    EtaleDerived X Λ ⥤ DerivedCategory (ModuleCat.{u} Λ) :=
  RightDerived.Cochain.functor
    ((sheafSections X.smallEtaleTopology (ModuleCat.{u} Λ)).obj
      (op (globalEtale X)))

/-- `RΓ(X, -)` is the cochain-level total right derived functor of sections at
the terminal object of `X_étale`. -/
theorem etaleDerivedGamma_def :
    etaleDerivedGamma X Λ =
      RightDerived.Cochain.functor
        ((sheafSections X.smallEtaleTopology (ModuleCat.{u} Λ)).obj
          (op (globalEtale X))) := sorry

end DerivedGamma

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

/-- Compactly supported derived sections `RΓ_c(X, -)` of a separated finite-type
scheme over a field, defined by `RΓ(Spec k, Rf_! -)` for the structure
morphism `f`. The source reads this on `D⁺_tors(X_étale, Λ)`, or on all of
`D(X_étale, Λ)` when `Λ` is torsion. -/
def etaleDerivedGammaCompactSupport :
    EtaleDerived X.left Λ ⥤ DerivedCategory (ModuleCat.{u} Λ) :=
  etaleDerivedLowerShriek X P ⋙
    etaleDerivedGamma (Spec (CommRingCat.of k)) Λ

/-- Compactly supported derived sections evaluate as `RΓ(Spec k, Rf_! K)`. -/
theorem etaleDerivedGammaCompactSupport_obj (K : EtaleDerived X.left Λ) :
    (etaleDerivedGammaCompactSupport P).obj K =
      (etaleDerivedGamma (Spec (CommRingCat.of k)) Λ).obj
        ((etaleDerivedLowerShriek X P).obj K) := sorry

/-- Compactly supported étale cohomology `H^i_c(X, K)` is the degree-`i`
homology of `RΓ_c(X, K)`. -/
def etaleDerivedCohomologyCompactSupport (i : ℤ) (K : EtaleDerived X.left Λ) :
    ModuleCat.{u} Λ :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} Λ) i).obj
    ((etaleDerivedGammaCompactSupport P).obj K)

/-- Compactly supported cohomology is homology of compactly supported derived
sections. -/
theorem etaleDerivedCohomologyCompactSupport_eq
    (i : ℤ) (K : EtaleDerived X.left Λ) :
    etaleDerivedCohomologyCompactSupport P i K =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} Λ) i).obj
        ((etaleDerivedGammaCompactSupport P).obj K) := sorry

end CompactSupport

end AlgebraicGeometry.Scheme.Etale

end
