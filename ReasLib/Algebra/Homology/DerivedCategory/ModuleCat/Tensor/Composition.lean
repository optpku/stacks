module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.ChangeOfRings
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Composition
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.FixedRight
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Associativity
import Mathlib.Tactic.CrossRefAttribute

/-!
# Three-ring composition for derived tensor change of rings

@stack 08YU

This leaf owns the aligned-universe functor comparison for a tower of commutative rings.  The
ambient fixed-right model is an explicit parameter: no monoidal structure or model is rebuilt by
typeclass search.  The raw `derivedTensorChangeOfRings` owner remains the source of the
algebra-map notation; this API keeps the ring homomorphisms explicit for reuse.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.DerivedTensor.ChangeOfRings

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
variable [MonoidalCategory (DerivedCategory (ModuleCat C))]

-- Implementation-only syntax shorthands; the public declarations elaborate to the canonical
-- fixed-right tensor and scalar-extension owners.
local notation "DTP" => DerivedCategory.derivedTensorProduct
local notation "Ext" => ModuleCat.derivedExtensionOfScalars

/-- The `C`-derived tensor of the scalar extension of `N` with `K`, used as the right factor in
the direct change-of-rings functor. -/
@[stacks 08YU "derived tensor of the transported middle and final factors"]
noncomputable abbrev rightFactor
    (τ : B →+* C) (N : DerivedCategory (ModuleCat B))
    (K : DerivedCategory (ModuleCat C)) : DerivedCategory (ModuleCat C) :=
  (DTP K).obj ((Ext τ).obj N)

/-- Lemma 15.60.5 (08YU): iterated derived tensor change of rings is identified with direct
change of rings along the composite map.  The comparison is built from the fixed-right
projection formula, scalar-extension composition, and the explicit fixed-right associator `T`.
-/
@[stacks 08YU "three-ring derived tensor composition"]
noncomputable def compIso
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat C))
    (σ : A →+* B) (τ : B →+* C)
    (N : DerivedCategory (ModuleCat B)) (K : DerivedCategory (ModuleCat C)) :
    CategoryTheory.derivedTensorChangeOfRings σ N ⋙
        CategoryTheory.derivedTensorChangeOfRings τ K ≅
      CategoryTheory.derivedTensorChangeOfRings (τ.comp σ) (rightFactor τ N K) :=
  Functor.associator (Ext σ) (DTP N) (Ext τ ⋙ DTP K) ≪≫
    Functor.isoWhiskerLeft (Ext σ)
      (Functor.associator (DTP N) (Ext τ) (DTP K)).symm ≪≫
    Functor.isoWhiskerLeft (Ext σ)
      (Functor.isoWhiskerRight
        (ModuleCat.DerivedExtension.Tensor.FixedRight.comparisonIso τ N)
        (DTP K)) ≪≫
    Functor.isoWhiskerLeft (Ext σ)
      (Functor.associator (Ext τ) (DTP ((Ext τ).obj N)) (DTP K)) ≪≫
    (Functor.associator (Ext σ) (Ext τ)
      (DTP ((Ext τ).obj N) ⋙ DTP K)).symm ≪≫
    Functor.isoWhiskerRight
      (ModuleCat.DerivedExtension.Composition.iso σ τ)
      (DTP ((Ext τ).obj N) ⋙ DTP K) ≪≫
    Functor.isoWhiskerLeft (Ext (τ.comp σ))
      (CategoryTheory.DerivedCategory.DerivedTensor.Right.tensorAssoc T
        ((Ext τ).obj N) K)

/-- The objectwise three-ring comparison supplied by `compIso`. -/
@[stacks 08YU "objectwise three-ring derived tensor composition"]
noncomputable abbrev compIsoApp
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat C))
    (σ : A →+* B) (τ : B →+* C)
    (N : DerivedCategory (ModuleCat B)) (K : DerivedCategory (ModuleCat C))
    (M : DerivedCategory (ModuleCat A)) :
    (CategoryTheory.derivedTensorChangeOfRings τ K).obj
        ((CategoryTheory.derivedTensorChangeOfRings σ N).obj M) ≅
      (CategoryTheory.derivedTensorChangeOfRings (τ.comp σ) (rightFactor τ N K)).obj M :=
  (compIso T σ τ N K).app M

/-- The object comparison in the base-change form
`(M ⊗[A] C) ⊗[C] (N ⊗[B] K)`. -/
@[stacks 08YU "base-change form of three-ring derived tensor composition"]
noncomputable def baseChangeIso
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat C))
    (σ : A →+* B) (τ : B →+* C)
    (N : DerivedCategory (ModuleCat B)) (K : DerivedCategory (ModuleCat C))
    (M : DerivedCategory (ModuleCat A)) :
    (CategoryTheory.derivedTensorChangeOfRings τ K).obj
        ((CategoryTheory.derivedTensorChangeOfRings σ N).obj M) ≅
      (DTP (rightFactor τ N K)).obj ((Ext (τ.comp σ)).obj M) :=
  compIsoApp T σ τ N K M ≪≫
    CategoryTheory.derivedTensorChangeOfRingsObjIso
      (τ.comp σ) (rightFactor τ N K) M

/-- The signed interchange comparison
`(M ⊗[A] N) ⊗[B] K ≅ (M ⊗[A] K) ⊗[C] (N ⊗[B] C)`. -/
@[stacks 08YU "signed derived tensor interchange"]
noncomputable def interchangeIso
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat C))
    (σ : A →+* B) (τ : B →+* C)
    (N : DerivedCategory (ModuleCat B)) (K : DerivedCategory (ModuleCat C))
    (M : DerivedCategory (ModuleCat A)) :
    (CategoryTheory.derivedTensorChangeOfRings τ K).obj
        ((CategoryTheory.derivedTensorChangeOfRings σ N).obj M) ≅
      (DTP ((Ext τ).obj N)).obj
        ((CategoryTheory.derivedTensorChangeOfRings (τ.comp σ) K).obj M) :=
  baseChangeIso T σ τ N K M ≪≫
    DerivedTensorProduct.objIsoBifunctor
      ((Ext (τ.comp σ)).obj M) (rightFactor τ N K) ≪≫
    (DerivedTensor.Bifunctor.functor (C := ModuleCat C)).mapIso
      (Iso.prod (Iso.refl _)
        (DerivedTensorProduct.comm ((Ext τ).obj N) K)) ≪≫
    (DerivedTensorProduct.objIsoBifunctor
      ((Ext (τ.comp σ)).obj M) ((DTP ((Ext τ).obj N)).obj K)).symm ≪≫
    (DerivedTensor.Right.assoc T ((Ext (τ.comp σ)).obj M) K ((Ext τ).obj N)).symm

end CategoryTheory.DerivedCategory.DerivedTensor.ChangeOfRings
