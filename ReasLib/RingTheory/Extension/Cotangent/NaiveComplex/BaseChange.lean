/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Tensor
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change models for naive cotangent complexes

This leaf separates the literal extension-of-scalars construction from the
two-term tensor model on which cotangent base-change maps are naturally
defined.  It is independent of localization and of any chapter-specific
presentation.  The local `Algebra.TensorProduct.Right` scope fixes the
ambient `T`-algebra structure on the first tensor factor; making that choice
global would introduce competing canonical scalar structures.  The paired
`SMulCommClass` instance is needed by `LinearMap.baseChange` for this fixed
interpretation.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct Algebra.TensorProduct.Right

universe u v w

noncomputable section

namespace Algebra.Extension.NaiveCotangent

variable {R : Type u} {S T : Type v}
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

-- Local instance justification (instance diamond): `LinearMap.baseChange` needs the
-- `SMulCommClass` for the fixed `Algebra.TensorProduct.Right` interpretation; global registration
-- would create a competing scalar structure for unrelated tensor models.
attribute [local instance] SMulCommClass.of_commMonoid

namespace BaseChange

/-- The literal scalar extension of a naive cotangent complex along `S → T`. -/
@[stacks 08JZ "literal scalar extension"]
noncomputable abbrev scalarExtension (P : Extension.{w} R S) :
    ChainComplex (ModuleCat.{max v w} T) ℕ :=
  ((ModuleCat.extendScalars (algebraMap S T)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (complex P)

/-- The explicit two-term tensor model for the scalar extension of a naive cotangent complex.
Its degree-one term is written using `P.Cotangent`, rather than a universe lift of it. -/
@[stacks 08JZ "two-term tensor model"]
noncomputable def tensorModel (P : Extension.{w} R S) :
    ChainComplex (ModuleCat.{max v w} T) ℕ :=
  ChainComplex.mk'
    (ModuleCat.of T (T ⊗[S] P.CotangentSpace))
    (ModuleCat.of T (T ⊗[S] P.Cotangent))
    (ModuleCat.ofHom (LinearMap.baseChange T P.cotangentComplex))
    (fun {_ _} _ ↦ ⟨ModuleCat.of T PUnit, 0, zero_comp⟩)

namespace ScalarExtension

/-- The componentwise normalization from literal scalar extension to the explicit tensor model.
The degree-zero and degree-one maps are the standard scalar-extension tensor isomorphisms, and
the remaining zero components are identified concretely. -/
noncomputable def componentIso (P : Extension.{w} R S) :
    ∀ n : ℕ,
      (scalarExtension (T := T) P).X n ≅ (tensorModel (T := T) P).X n
  | 0 => by
      simpa [scalarExtension, tensorModel, complex] using
        ModuleCat.ExtendScalars.tensorIso (R := S) (S := T)
          (ModuleCat.of S P.CotangentSpace)
  | 1 => by
      simpa [scalarExtension, tensorModel, complex] using
        (ModuleCat.ExtendScalars.tensorIso (R := S) (S := T)
          (ModuleCat.of S (Lift P))) ≪≫
          (TensorProduct.AlgebraTensorModule.congr
            (LinearEquiv.refl T T) (liftEquiv P)).toModuleIso
  | n + 2 => by
      let hX :
          (scalarExtension (T := T) P).X (n + 2) =
            (ModuleCat.extendScalars (algebraMap S T)).obj ((complex P).X (n + 2)) :=
        CategoryTheory.Functor.mapHomologicalComplex_obj_X
          (ModuleCat.extendScalars (algebraMap S T)) (ComplexShape.down ℕ) (complex P) (n + 2)
      have hsrc :
          (scalarExtension (T := T) P).X (n + 2) ≅ ModuleCat.of T PUnit := by
        simpa [scalarExtension] using
          eqToIso hX ≪≫
            (ModuleCat.extendScalars (algebraMap S T)).mapIso
              (componentSuccSuccIsoUnit P n) ≪≫
            ModuleCat.ExtendScalars.tensorIso (R := S) (S := T)
              (ModuleCat.of S PUnit) ≪≫
            ModuleCat.ExtendScalars.tensorPUnitIso (R := S) (S := T)
      have htrg :
          (tensorModel (T := T) P).X (n + 2) ≅ ModuleCat.of T PUnit := by
        simpa [tensorModel] using
          (ChainComplex.mk'XIso
            (ModuleCat.of T (T ⊗[S] P.CotangentSpace))
            (ModuleCat.of T (T ⊗[S] P.Cotangent))
            (ModuleCat.ofHom (LinearMap.baseChange T P.cotangentComplex))
            (fun {_ _} _ ↦ ⟨ModuleCat.of T PUnit, 0, zero_comp⟩) n)
      exact hsrc ≪≫ htrg.symm

/-- The componentwise normalization commutes with the differentials. -/
theorem componentIso_comm (P : Extension.{w} R S) :
    ∀ i j (_ : (ComplexShape.down ℕ).Rel i j),
      (componentIso (T := T) P i).hom ≫ (tensorModel (T := T) P).d i j =
        (scalarExtension (T := T) P).d i j ≫ (componentIso (T := T) P j).hom := sorry

end ScalarExtension

/-- The literal scalar extension of a naive cotangent complex is canonically isomorphic to its
explicit two-term tensor model. -/
@[stacks 08JZ "scalar-extension tensor normalization"]
noncomputable def scalarExtensionIsoTensorModel (P : Extension.{w} R S) :
    scalarExtension (T := T) P ≅ tensorModel (T := T) P :=
  HomologicalComplex.Hom.isoOfComponents
    (ScalarExtension.componentIso (T := T) P)
    (ScalarExtension.componentIso_comm (T := T) P)

section Composition

variable {ι κ : Type w}

namespace ToComp

/-- The degree-zero map from the tensor model of `P` to the naive cotangent complex of the
composed presentation `Q.comp P`. -/
noncomputable def zero
    (P : Algebra.Generators R S ι) (Q : Algebra.Generators S T κ) :
    (tensorModel P.toExtension).X 0 ⟶ (complex (Q.comp P).toExtension).X 0 :=
  ModuleCat.ofHom
    (LinearMap.liftBaseChange T
      (CotangentSpace.map (Q.toComp P).toExtensionHom))

/-- The degree-one map from the tensor model of `P` to the naive cotangent complex of the
composed presentation `Q.comp P`. -/
noncomputable def one
    (P : Algebra.Generators R S ι) (Q : Algebra.Generators S T κ) :
    (tensorModel P.toExtension).X 1 ⟶ (complex (Q.comp P).toExtension).X 1 :=
  ModuleCat.ofHom
    ((liftEquiv (Q.comp P).toExtension).symm.toLinearMap ∘ₗ
      LinearMap.liftBaseChange T (Cotangent.map (Q.toComp P).toExtensionHom))

/-- The degree-one and degree-zero components of `toComp` commute with their differentials. -/
theorem oneZeroComm
    (P : Algebra.Generators R S ι) (Q : Algebra.Generators S T κ) :
    one P Q ≫ (complex (Q.comp P).toExtension).d 1 0 =
      (tensorModel P.toExtension).d 1 0 ≫ zero P Q := sorry

/-- The zero higher component satisfies the chain-map compatibility condition for `toComp`. -/
theorem succComm
    (P : Algebra.Generators R S ι) (Q : Algebra.Generators S T κ) (n : ℕ)
    (p :
      Σ' (zero : (tensorModel P.toExtension).X n ⟶ (complex (Q.comp P).toExtension).X n)
          (one : (tensorModel P.toExtension).X (n + 1) ⟶
            (complex (Q.comp P).toExtension).X (n + 1)),
        one ≫ (complex (Q.comp P).toExtension).d (n + 1) n =
          (tensorModel P.toExtension).d (n + 1) n ≫ zero) :
    (0 : (tensorModel P.toExtension).X (n + 2) ⟶
        (complex (Q.comp P).toExtension).X (n + 2)) ≫
        (complex (Q.comp P).toExtension).d (n + 2) (n + 1) =
      (tensorModel P.toExtension).d (n + 2) (n + 1) ≫ p.2.1 := sorry

/-- The higher components of the natural map from the tensor model to a composed presentation. -/
noncomputable def succ
    (P : Algebra.Generators R S ι) (Q : Algebra.Generators S T κ) (n : ℕ)
    (p :
      Σ' (zero : (tensorModel P.toExtension).X n ⟶ (complex (Q.comp P).toExtension).X n)
          (one : (tensorModel P.toExtension).X (n + 1) ⟶
            (complex (Q.comp P).toExtension).X (n + 1)),
        one ≫ (complex (Q.comp P).toExtension).d (n + 1) n =
          (tensorModel P.toExtension).d (n + 1) n ≫ zero) :
    Σ' two : (tensorModel P.toExtension).X (n + 2) ⟶
        (complex (Q.comp P).toExtension).X (n + 2),
      two ≫ (complex (Q.comp P).toExtension).d (n + 2) (n + 1) =
        (tensorModel P.toExtension).d (n + 2) (n + 1) ≫ p.2.1 :=
  ⟨0, succComm P Q n p⟩

end ToComp

/-- The natural chain map from the tensor model of `P` to the naive cotangent complex of the
composed presentation `Q.comp P`. -/
@[stacks 08JZ "base-change map to a composed presentation"]
noncomputable def toComp
    (P : Algebra.Generators R S ι) (Q : Algebra.Generators S T κ) :
    tensorModel P.toExtension ⟶ complex (Q.comp P).toExtension :=
  ChainComplex.mkHom _ _
    (ToComp.zero P Q)
    (ToComp.one P Q)
    (ToComp.oneZeroComm P Q)
    (ToComp.succ P Q)

end Composition

end BaseChange

end Algebra.Extension.NaiveCotangent
