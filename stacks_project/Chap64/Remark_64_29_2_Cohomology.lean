module

public import Mathlib.CategoryTheory.Sites.Whiskering
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.FixedInterior
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import stacks_project.Chap58.Lemma_58_14_3_Induced
public import stacks_project.Chap59.Definition_59_70_1_ExtensionByZero
public import stacks_project.Chap59.Lemma_59_59_2

/-!
# Module-valued geometric étale cohomology

This leaf owns ordinary and compactly supported geometric étale cohomology of a
sheaf of `Λ`-modules, extracted as site cohomology of the restriction to
`X_k̄` (respectively of the extension by zero along a compactification).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.SchemeOverField
open Opposite
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable {Λ : Type (u + 1)} [CommRing Λ]
variable (X : SchemeOverField k)

variable [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [HasWeakSheafify (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ P : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (smallEtalePullback (geometricToArithmeticHom X)).op.HasLeftKanExtension P]
variable [HasSheafify (geometricBaseChange X).smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasExt (Sheaf (geometricBaseChange X).smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [(geometricBaseChange X).smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})]

/-- Restriction of a sheaf of `Λ`-modules to the geometric fibre `X_k̄`. -/
def geometricModuleRestriction
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Sheaf (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  ((smallEtalePullback (geometricToArithmeticHom X)).sheafPullback (ModuleCat.{u + 1} Λ)
      X.left.smallEtaleTopology (geometricBaseChange X).smallEtaleTopology).obj F

/-- Unfolding of geometric restriction as small-étale sheaf pullback along
`X_k̄ ⟶ X`. -/
theorem geometricModuleRestriction_eq
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    geometricModuleRestriction X F =
      ((smallEtalePullback (geometricToArithmeticHom X)).sheafPullback (ModuleCat.{u + 1} Λ)
          X.left.smallEtaleTopology (geometricBaseChange X).smallEtaleTopology).obj F :=
  rfl

/-- Geometric étale cohomology `H^j(X_k̄, F|_{X_k̄})` of a sheaf of `Λ`-modules. -/
def geometricModuleEtaleHq
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (j : ℕ) :
    ModuleCat.{u + 1} Λ :=
  (siteModuleCohomologyModuleFunctor
      (J := (geometricBaseChange X).smallEtaleTopology) (A := Λ) j).obj
    (geometricModuleRestriction X F)

/-- Unfolding of module-valued geometric cohomology as the module-valued site
cohomology functor of the geometric restriction. -/
theorem geometricModuleEtaleHq_eq
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (j : ℕ) :
    geometricModuleEtaleHq X F j =
      (siteModuleCohomologyModuleFunctor
          (J := (geometricBaseChange X).smallEtaleTopology) (A := Λ) j).obj
        (geometricModuleRestriction X F) :=
  rfl

/-- The map on geometric étale cohomology induced by a morphism of sheaves of
`Λ`-modules. -/
def geometricModuleEtaleHqMap
    {F G : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ⟶ G) (j : ℕ) :
    geometricModuleEtaleHq X F j ⟶ geometricModuleEtaleHq X G j :=
  (siteModuleCohomologyModuleFunctor
      (J := (geometricBaseChange X).smallEtaleTopology) (A := Λ) j).map
    (((smallEtalePullback (geometricToArithmeticHom X)).sheafPullback (ModuleCat.{u + 1} Λ)
        X.left.smallEtaleTopology (geometricBaseChange X).smallEtaleTopology).map φ)

/-- Unfolding of the induced map on geometric étale cohomology. -/
theorem geometricModuleEtaleHqMap_eq
    {F G : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ⟶ G) (j : ℕ) :
    geometricModuleEtaleHqMap X φ j =
      (siteModuleCohomologyModuleFunctor
          (J := (geometricBaseChange X).smallEtaleTopology) (A := Λ) j).map
        (((smallEtalePullback (geometricToArithmeticHom X)).sheafPullback (ModuleCat.{u + 1} Λ)
            X.left.smallEtaleTopology (geometricBaseChange X).smallEtaleTopology).map φ) :=
  rfl

variable (P : Compactification.Of (Spec (CommRingCat.of k)) X)
variable [Etale (Compactification.Of.ι P)]
variable [HasWeakSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [HasWeakSheafify
    (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom).smallEtaleTopology
    (ModuleCat.{u + 1} Λ)]
variable [∀ G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
variable [∀ G : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (smallEtalePullback
        (FieldExtension.toSource k (AlgebraicClosure k) P.obj.right.hom)).op.HasLeftKanExtension G]
variable [HasSheafify
    (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom).smallEtaleTopology
    AddCommGrpCat.{u + 1}]
variable [HasExt
    (Sheaf
      (FieldExtension.baseChange k (AlgebraicClosure k)
        P.obj.right.hom).smallEtaleTopology
      AddCommGrpCat.{u + 1})]
variable [(FieldExtension.baseChange k (AlgebraicClosure k)
      P.obj.right.hom).smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})]

/-- Extension by zero of a sheaf of `Λ`-modules along the interior of a compactification. -/
def geometricModuleExtensionByZero
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u + 1} Λ)).obj F

/-- Unfolding of extension by zero along `Compactification.Of.ι P`. -/
theorem geometricModuleExtensionByZero_eq
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    geometricModuleExtensionByZero X P F =
      (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u + 1} Λ)).obj F :=
  rfl

/-- Geometric restriction of the extension by zero, as a sheaf on the geometric fibre of
the compactification. -/
def geometricModuleRestrictionCompactSupport
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Sheaf
      (FieldExtension.baseChange k (AlgebraicClosure k)
        P.obj.right.hom).smallEtaleTopology
      (ModuleCat.{u + 1} Λ) :=
  ((smallEtalePullback
        (FieldExtension.toSource k (AlgebraicClosure k) P.obj.right.hom)).sheafPullback
      (ModuleCat.{u + 1} Λ) P.obj.right.left.smallEtaleTopology
      (FieldExtension.baseChange k (AlgebraicClosure k)
        P.obj.right.hom).smallEtaleTopology).obj
    (geometricModuleExtensionByZero X P F)

/-- Unfolding of compactly supported geometric restriction as pullback of `j_! F`. -/
theorem geometricModuleRestrictionCompactSupport_eq
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    geometricModuleRestrictionCompactSupport X P F =
      ((smallEtalePullback
            (FieldExtension.toSource k (AlgebraicClosure k)
              P.obj.right.hom)).sheafPullback
          (ModuleCat.{u + 1} Λ) P.obj.right.left.smallEtaleTopology
          (FieldExtension.baseChange k (AlgebraicClosure k)
            P.obj.right.hom).smallEtaleTopology).obj
        (geometricModuleExtensionByZero X P F) :=
  rfl

/-- Compactly supported geometric étale cohomology `H_c^j(X_k̄, F)` of a sheaf of
`Λ`-modules. -/
def geometricModuleEtaleHqCompactSupport
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (j : ℕ) :
    ModuleCat.{u + 1} Λ :=
  (siteModuleCohomologyModuleFunctor
      (J := (FieldExtension.baseChange k (AlgebraicClosure k)
          P.obj.right.hom).smallEtaleTopology)
      (A := Λ) j).obj
    (geometricModuleRestrictionCompactSupport X P F)

/-- Unfolding of compactly supported geometric cohomology as the module-valued site
cohomology functor of `j_! F` on the geometric fibre of the compactification. -/
theorem geometricModuleEtaleHqCompactSupport_eq
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (j : ℕ) :
    geometricModuleEtaleHqCompactSupport X P F j =
      (siteModuleCohomologyModuleFunctor
          (J := (FieldExtension.baseChange k (AlgebraicClosure k)
              P.obj.right.hom).smallEtaleTopology)
          (A := Λ) j).obj
        (geometricModuleRestrictionCompactSupport X P F) :=
  rfl

/-- The map on compactly supported geometric étale cohomology induced by a morphism of
sheaves of `Λ`-modules. -/
def geometricModuleEtaleHqCompactSupportMap
    {F G : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ⟶ G) (j : ℕ) :
    geometricModuleEtaleHqCompactSupport X P F j ⟶
      geometricModuleEtaleHqCompactSupport X P G j :=
  (siteModuleCohomologyModuleFunctor
      (J := (FieldExtension.baseChange k (AlgebraicClosure k)
          P.obj.right.hom).smallEtaleTopology)
      (A := Λ) j).map
    (((smallEtalePullback
          (FieldExtension.toSource k (AlgebraicClosure k)
            P.obj.right.hom)).sheafPullback
        (ModuleCat.{u + 1} Λ) P.obj.right.left.smallEtaleTopology
        (FieldExtension.baseChange k (AlgebraicClosure k)
          P.obj.right.hom).smallEtaleTopology).map
      ((etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u + 1} Λ)).map φ))

/-- Unfolding of the induced map on compactly supported geometric cohomology. -/
theorem geometricModuleEtaleHqCompactSupportMap_eq
    {F G : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ⟶ G) (j : ℕ) :
    geometricModuleEtaleHqCompactSupportMap X P φ j =
      (siteModuleCohomologyModuleFunctor
          (J := (FieldExtension.baseChange k (AlgebraicClosure k)
              P.obj.right.hom).smallEtaleTopology)
          (A := Λ) j).map
        (((smallEtalePullback
              (FieldExtension.toSource k (AlgebraicClosure k)
                P.obj.right.hom)).sheafPullback
            (ModuleCat.{u + 1} Λ) P.obj.right.left.smallEtaleTopology
            (FieldExtension.baseChange k (AlgebraicClosure k)
              P.obj.right.hom).smallEtaleTopology).map
          ((etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u + 1} Λ)).map φ)) :=
  rfl

/-- Compactly supported geometric cohomology is independent of the choice of
compactification. -/
theorem geometricModuleEtaleHqCompactSupport_independent
    {Q : Compactification.Of (Spec (CommRingCat.of k)) X}
    [Etale (Compactification.Of.ι Q)]
    (f : P ⟶ Q)
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (j : ℕ) :
    Nonempty
      (geometricModuleEtaleHqCompactSupport X P F j ≅
        geometricModuleEtaleHqCompactSupport X Q F j) :=
  sorry

end AlgebraicGeometry.SchemeOverField
