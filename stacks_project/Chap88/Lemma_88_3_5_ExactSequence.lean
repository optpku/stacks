/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Homology
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Tensor
public import stacks_project.Chap88.«88_3_0_1»
public import stacks_project.Chap88.Lemma_88_3_5_Presentation

/-!
# Jacobi–Zariski maps of completed naive cotangent complexes

This leaf owns the scalar extension of `NL_{B/A}^∧`, the chain maps induced by
a composite presentation, and the five homology maps of the six-term sequence.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open Algebra.Extension
open Algebra.NaiveCotangent.Adic
open scoped TensorProduct

namespace Algebra.NaiveCotangent.Adic

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [IsNoetherianRing A]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
variable (I : Ideal A) [Algebra.TopologicallyFiniteType I C]
variable {ι κ : Type u}

/-- The map on free generators sending `dx_i` to the corresponding generator of
the composite presentation. -/
def toCompOnVars :
    (ι → B) →ₗ[B] ((κ ⊕ ι) → C) :=
  LinearMap.pi (Sum.elim (fun _ ↦ 0)
    (fun i ↦ (Algebra.linearMap B C).comp (LinearMap.proj i)))

/-- The map on free generators restricting composite differentials to the
`y`-variables. -/
def ofCompOnVars :
    ((κ ⊕ ι) → C) →ₗ[C] (κ → C) :=
  LinearMap.funLeft C C Sum.inl

/-- `toCompOnVars` is zero on `y`-coordinates and applies `algebraMap B C` on
`x`-coordinates. -/
theorem toCompOnVars_apply (dx : ι → B) (x : κ ⊕ ι) :
    toCompOnVars dx x =
      Sum.elim (fun _ ↦ (0 : C)) (fun i ↦ algebraMap B C (dx i)) x := sorry

/-- `ofCompOnVars` is precomposition with `Sum.inl`. -/
theorem ofCompOnVars_apply (dy : (κ ⊕ ι) → C) (j : κ) :
    ofCompOnVars dy j = dy (Sum.inl j) := sorry

variable [Fintype ι] [Fintype κ]
variable (P : Presentation A B I ι)
variable (Q : Presentation B C (I.map (algebraMap A B)) κ)

/-- The scalar extension `NL_{B/A}^∧ ⊗_B C` of a completed naive cotangent
complex. -/
def tensorComplex :
    ChainComplex (ModuleCat C) ℕ :=
  ((ModuleCat.extendScalars (algebraMap B C)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
    (naiveCotangent I P)

/-- The differential of `NL_{B/A}^∧ ⊗_B C` in degrees `1 → 0` is the scalar
extension of the Jacobian of `P`. -/
theorem tensorComplex_d_one_zero :
    (tensorComplex I P).d 1 0 =
      (ModuleCat.extendScalars (algebraMap B C)).map ((naiveCotangent I P).d 1 0) := sorry

/-- The chain map `NL_{B/A}^∧ ⊗_B C ⟶ NL_{C/A}^∧` induced by `toComp`. -/
def toCompChainMap :
    tensorComplex I P ⟶ naiveCotangent I (Q.comp P) where
  f
    | 0 =>
        (ModuleCat.ExtendScalars.tensorIso (R := B) (S := C)
            ((naiveCotangent I P).X 0)).hom ≫
          ModuleCat.ofHom ((toCompOnVars (κ := κ) (ι := ι)).liftBaseChange C)
    | 1 =>
        (ModuleCat.ExtendScalars.tensorIso (R := B) (S := C)
            ((naiveCotangent I P).X 1)).hom ≫
          ModuleCat.ofHom ((Cotangent.map (Presentation.toCompHom Q P)).liftBaseChange C)
    | _ + 2 => 0
  comm' := sorry

/-- The chain map `NL_{C/A}^∧ ⟶ NL_{C/B}^∧` induced by `ofComp`. -/
def ofCompChainMap :
    naiveCotangent I (Q.comp P) ⟶ naiveCotangent (I.map (algebraMap A B)) Q where
  f
    | 0 => ModuleCat.ofHom (ofCompOnVars (κ := κ) (ι := ι))
    | 1 => ModuleCat.ofHom (Cotangent.map (Presentation.ofCompHom Q P))
    | _ + 2 => 0
  comm' := sorry

/-- The unit of extension of scalars, as a chain map
`NL_{B/A}^∧ ⟶ restrict (NL_{B/A}^∧ ⊗_B C)`. -/
def unitChainMap :
    naiveCotangent I P ⟶
      ((ModuleCat.restrictScalars (algebraMap B C)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj
        (tensorComplex I P) where
  f n := (ModuleCat.extendRestrictScalarsAdj (algebraMap B C)).unit.app
    ((naiveCotangent I P).X n)
  comm' := sorry

/-- The comparison `C ⊗[B] H^0(NL_{B/A}^∧) ⟶ H^0(NL_{B/A}^∧ ⊗_B C)`. -/
def homologyZero_tensor_to :
    ModuleCat.of C (C ⊗[B] ((naiveCotangent I P).homology 0 : Type u)) ⟶
      (tensorComplex I P).homology 0 :=
  (ModuleCat.ExtendScalars.tensorIso (R := B) (S := C)
      ((naiveCotangent I P).homology 0)).inv ≫
    ((ModuleCat.extendRestrictScalarsAdj (algebraMap B C)).homEquiv _ _).symm
      (HomologicalComplex.homologyMap (unitChainMap I P) 0 ≫
        (ModuleCat.restrictScalarsHomologyIso (algebraMap B C) (tensorComplex I P) 0).hom)

/-- The comparison `H^0(NL_{B/A}^∧ ⊗_B C) ⟶ C ⊗[B] H^0(NL_{B/A}^∧)` induced by
right exactness of extension of scalars. -/
def homologyZero_tensor_from :
    (tensorComplex I P).homology 0 ⟶
      ModuleCat.of C (C ⊗[B] ((naiveCotangent I P).homology 0 : Type u)) :=
  (tensorComplex I P).isoHomologyι₀.hom ≫
    (tensorComplex I P).descOpcycles
      ((ModuleCat.extendScalars (algebraMap B C)).map
          ((naiveCotangent I P).pOpcycles 0 ≫
            (naiveCotangent I P).isoHomologyι₀.inv) ≫
        (ModuleCat.ExtendScalars.tensorIso (R := B) (S := C)
            ((naiveCotangent I P).homology 0)).hom)
      1 (ChainComplex.prev ℕ 0) sorry

/-- Right exactness of `C ⊗[B] -` identifies `H^0(NL_{B/A}^∧ ⊗_B C)` with
`C ⊗[B] H^0(NL_{B/A}^∧)`. Both directions are the explicit cokernel comparisons. -/
def homologyZero_tensor_iso :
    (tensorComplex I P).homology 0 ≅
      ModuleCat.of C (C ⊗[B] ((naiveCotangent I P).homology 0 : Type u)) where
  hom := homologyZero_tensor_from I P
  inv := homologyZero_tensor_to I P
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The two-term Jacobi–Zariski short complex of completed naive cotangent
complexes attached to a composite presentation. -/
def jacobiZariskiShortComplex :
    ShortComplex (ChainComplex (ModuleCat C) ℕ) :=
  ShortComplex.mk (toCompChainMap I P Q) (ofCompChainMap I P Q) sorry

/-- The Jacobi–Zariski short complex of completed naive cotangent complexes is
short exact. -/
theorem jacobiZariskiShortExact :
    (jacobiZariskiShortComplex I P Q).ShortExact := sorry

/-- The first arrow of the six-term sequence, from
`H^{-1}(NL_{B/A}^∧ ⊗_B C)` to `H^{-1}(NL_{C/A}^∧)`. -/
def homologyOneTensor :
    (tensorComplex I P).homology 1 ⟶ (naiveCotangent I (Q.comp P)).homology 1 :=
  HomologicalComplex.homologyMap (toCompChainMap I P Q) 1

/-- The map `H^{-1}(NL_{C/A}^∧) ⟶ H^{-1}(NL_{C/B}^∧)`. -/
def homologyOneMap :
    (naiveCotangent I (Q.comp P)).homology 1 ⟶
      (naiveCotangent (I.map (algebraMap A B)) Q).homology 1 :=
  HomologicalComplex.homologyMap (ofCompChainMap I P Q) 1

/-- A set-theoretic section of `Cotangent.map ofCompHom`, used as the snake
lift through the composite presentation. -/
def ofCompCotangentSection :
    Q.toExtension.Cotangent → (Q.comp P).toExtension.Cotangent :=
  Function.invFun ⇑(Cotangent.map (Presentation.ofCompHom Q P))

/-- A set-theoretic retraction of `toCompOnVars.liftBaseChange`, used as the
snake retraction on free generators. -/
def toCompOnVarsRetract :
    ((κ ⊕ ι) → C) → C ⊗[B] (ι → B) :=
  Function.invFun ⇑((toCompOnVars (κ := κ) (ι := ι)).liftBaseChange C)

/-- The quotient map `⊕ᵢ B dx_i ⟶ H^0(NL_{B/A}^∧)`. -/
def homologyZeroπ :
    ((naiveCotangent I P).X 0 : Type u) →ₗ[B]
      ((naiveCotangent I P).homology 0 : Type u) :=
  ((naiveCotangent I P).pOpcycles 0 ≫ (naiveCotangent I P).isoHomologyι₀.inv).hom

/-- The snake connecting map
`H^{-1}(NL_{C/B}^∧) ⟶ C ⊗[B] H^0(NL_{B/A}^∧)`, obtained by lifting through the
composite Jacobian column and retracting the free generators. -/
def δ :
    (naiveCotangent (I.map (algebraMap A B)) Q).homology 1 ⟶
      ModuleCat.of C (C ⊗[B] ((naiveCotangent I P).homology 0 : Type u)) :=
  ModuleCat.ofHom
    { toFun := fun x ↦
        (homologyZeroπ I P).baseChange C
          (Function.invFun ⇑((toCompOnVars (κ := κ) (ι := ι)).liftBaseChange C)
            (jacobian (Q.comp P)
              (Function.invFun ⇑(Cotangent.map (Presentation.ofCompHom Q P))
                (((naiveCotangent (I.map (algebraMap A B)) Q).iCycles 1).hom
                  (Function.invFun
                    (fun y ↦
                      ((naiveCotangent (I.map (algebraMap A B)) Q).homologyπ 1).hom y)
                    x)))))
      map_add' := sorry
      map_smul' := sorry }

/-- The map `H^0(NL_{B/A}^∧ ⊗_B C) ⟶ H^0(NL_{C/A}^∧)` induced by `toComp`. -/
def homologyZeroBaseChangeOpcycles :
    (tensorComplex I P).homology 0 ⟶ (naiveCotangent I (Q.comp P)).homology 0 :=
  HomologicalComplex.homologyMap (toCompChainMap I P Q) 0

/-- The map `C ⊗[B] H^0(NL_{B/A}^∧) ⟶ H^0(NL_{C/A}^∧)`. -/
def homologyZeroBaseChange :
    ModuleCat.of C (C ⊗[B] ((naiveCotangent I P).homology 0 : Type u)) ⟶
      (naiveCotangent I (Q.comp P)).homology 0 :=
  (homologyZero_tensor_iso I P).inv ≫ homologyZeroBaseChangeOpcycles I P Q

/-- The map `H^0(NL_{C/A}^∧) ⟶ H^0(NL_{C/B}^∧)`. -/
def homologyZeroMap :
    (naiveCotangent I (Q.comp P)).homology 0 ⟶
      (naiveCotangent (I.map (algebraMap A B)) Q).homology 0 :=
  HomologicalComplex.homologyMap (ofCompChainMap I P Q) 0

/-- The degree-one tensor comparison is the homology map of `toCompChainMap`. -/
theorem homologyOneTensor_eq :
    homologyOneTensor I P Q = HomologicalComplex.homologyMap (toCompChainMap I P Q) 1 := sorry

/-- The degree-zero source map is the tensor comparison followed by the
homology map of `toCompChainMap`. -/
theorem homologyZeroBaseChange_eq :
    homologyZeroBaseChange I P Q =
      (homologyZero_tensor_iso I P).inv ≫ homologyZeroBaseChangeOpcycles I P Q := sorry

/-- The connecting map kills the image of `homologyOneMap`. -/
theorem homologyOneMap_comp_δ :
    homologyOneMap I P Q ≫ δ I P Q = 0 := sorry

/-- The opcycle-level degree-zero map is the homology map of `toCompChainMap`. -/
theorem homologyZeroBaseChangeOpcycles_eq :
    homologyZeroBaseChangeOpcycles I P Q =
      HomologicalComplex.homologyMap (toCompChainMap I P Q) 0 := sorry

/-- The unit chain map in each degree is the adjunction unit. -/
theorem unitChainMap_f (n : ℕ) :
    (unitChainMap I P).f n =
      (ModuleCat.extendRestrictScalarsAdj (algebraMap B C)).unit.app
        ((naiveCotangent I P).X n) := sorry

end Algebra.NaiveCotangent.Adic


