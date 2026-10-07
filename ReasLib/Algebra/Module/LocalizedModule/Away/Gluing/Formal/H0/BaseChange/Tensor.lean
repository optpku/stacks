module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal.H0.BaseChange
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor Base Change for Formal Gluing and Degree-Zero Sections

The tensor-product square associated to two maps out of `R` specializes formal-gluing base change.
When both maps are flat, the canonical right mate on degree-zero sections is invertible.

@stack 05EQ
-/

@[expose] public section

open CategoryTheory

universe u

noncomputable section

namespace LocalizedModule.Away.FormalGluing

variable {R S Rp : Type u}
variable [CommRing R] [CommRing S] [CommRing Rp]
variable [Algebra R S] [Algebra R Rp]
variable {t : ℕ} (f : Fin t → R)

/-- The middle vertical functor in the formal-gluing tensor-base-change diagram. -/
@[stacks 05EQ "formal gluing tensor base-change functor"]
noncomputable abbrev tensorBaseChangeFunctor :
    FormalGluing.{u, 0, 0} (algebraMap R S) f ⥤
      FormalGluing
        (Algebra.TensorProduct.includeRight
          (R := R) (A := S) (B := Rp)).toRingHom
        (fun i ↦ algebraMap R Rp (f i)) :=
  baseChangeFunctor
    (algebraMap R S)
    (algebraMap R Rp)
    (Algebra.TensorProduct.includeLeftRingHom
      (R := R) (A := S) (B := Rp))
    (Algebra.TensorProduct.includeRight
      (R := R) (A := S) (B := Rp)).toRingHom
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := R) (A := S) (B := Rp))

/-- The left square in the tensor-base-change diagram, expressing that canonical formal gluing
commutes with extension of scalars to `Rp`. -/
@[stacks 05EQ "canonical formal gluing tensor base-change square"]
noncomputable abbrev canTensorBaseChangeIso :
    ModuleCat.extendScalars (algebraMap R Rp) ⋙
        ofModuleFunctor
          (Algebra.TensorProduct.includeRight
            (R := R) (A := S) (B := Rp)).toRingHom
          (fun i ↦ algebraMap R Rp (f i)) ≅
      ofModuleFunctor (algebraMap R S) f ⋙ tensorBaseChangeFunctor f :=
  canBaseChangeNatIso
    (algebraMap R S)
    (algebraMap R Rp)
    (Algebra.TensorProduct.includeLeftRingHom
      (R := R) (A := S) (B := Rp))
    (Algebra.TensorProduct.includeRight
      (R := R) (A := S) (B := Rp)).toRingHom
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := R) (A := S) (B := Rp))

/-- The right square in the tensor-base-change diagram, as the canonical right mate of
`canTensorBaseChangeIso`. -/
@[stacks 05EQ "formal gluing degree-zero tensor base-change map"]
noncomputable abbrev h0TensorBaseChange :
    h0Functor (φ := algebraMap R S) (f := f) ⋙
        ModuleCat.extendScalars (algebraMap R Rp) ⟶
      tensorBaseChangeFunctor f ⋙
        h0Functor
          (φ := (Algebra.TensorProduct.includeRight
            (R := R) (A := S) (B := Rp)).toRingHom)
          (f := fun i ↦ algebraMap R Rp (f i)) :=
  h0BaseChangeNatTrans
    (algebraMap R S)
    (algebraMap R Rp)
    (Algebra.TensorProduct.includeLeftRingHom
      (R := R) (A := S) (B := Rp))
    (Algebra.TensorProduct.includeRight
      (R := R) (A := S) (B := Rp)).toRingHom
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := R) (A := S) (B := Rp))

/-- Lemma 15.90.15 (05EQ): if both maps out of `R` are flat, every component of the canonical
degree-zero tensor-base-change mate is an isomorphism. -/
@[stacks 05EQ "Lemma 15.90.15"]
theorem h0TensorBaseChange_app_isIso
    (hφ : (algebraMap R S).Flat) (hψ : (algebraMap R Rp).Flat)
    (X : FormalGluing.{u, 0, 0} (algebraMap R S) f) :
    IsIso ((h0TensorBaseChange (R := R) (S := S) (Rp := Rp) f).app X) := sorry

end LocalizedModule.Away.FormalGluing
