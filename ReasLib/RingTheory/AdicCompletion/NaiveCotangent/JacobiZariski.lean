module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Homology
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Tensor
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.Presentation

/-!
# Jacobi–Zariski maps of completed naive cotangent complexes

The scalar extension of `NL_{B/A}^∧`, the chain maps induced by
a composite presentation, and the five homology maps form a six-term exact sequence.
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
variable (I : Ideal A) [hB : Algebra.TopologicallyFiniteType I B]
  [Algebra.TopologicallyFiniteType I C]
variable {ι κ : Type u}

omit hB

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
      Sum.elim (fun _ ↦ (0 : C)) (fun i ↦ algebraMap B C (dx i)) x := by
  cases x <;> rfl

/-- `ofCompOnVars` is precomposition with `Sum.inl`. -/
theorem ofCompOnVars_apply (dy : (κ ⊕ ι) → C) (j : κ) :
    ofCompOnVars dy j = dy (Sum.inl j) := rfl

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
      (ModuleCat.extendScalars (algebraMap B C)).map ((naiveCotangent I P).d 1 0) := rfl

/-- The scalar-extended variable inclusion commutes with the completed Jacobians. -/
private theorem toCompChainMap_comm (i j : ℕ) (h : (ComplexShape.down ℕ).Rel i j) :
    (fun n : ℕ ↦ (show (tensorComplex I P).X n ⟶ (naiveCotangent I (Q.comp P)).X n from
      match n with
    | 0 =>
        (ModuleCat.ExtendScalars.tensorIso (R := B) (S := C)
            ((naiveCotangent I P).X 0)).hom ≫
          ModuleCat.ofHom ((toCompOnVars (κ := κ) (ι := ι)).liftBaseChange C)
    | 1 =>
        (ModuleCat.ExtendScalars.tensorIso (R := B) (S := C)
            ((naiveCotangent I P).X 1)).hom ≫
          ModuleCat.ofHom ((Cotangent.map (Presentation.toCompHom Q P)).liftBaseChange C)
    | _ + 2 => 0
    )) i ≫ (naiveCotangent I (Q.comp P)).d i j =
      (tensorComplex I P).d i j ≫ (fun n : ℕ ↦ (show (tensorComplex I P).X n ⟶ (naiveCotangent I (Q.comp P)).X n from
      match n with
    | 0 =>
        (ModuleCat.ExtendScalars.tensorIso (R := B) (S := C)
            ((naiveCotangent I P).X 0)).hom ≫
          ModuleCat.ofHom ((toCompOnVars (κ := κ) (ι := ι)).liftBaseChange C)
    | 1 =>
        (ModuleCat.ExtendScalars.tensorIso (R := B) (S := C)
            ((naiveCotangent I P).X 1)).hom ≫
          ModuleCat.ofHom ((Cotangent.map (Presentation.toCompHom Q P)).liftBaseChange C)
    | _ + 2 => 0
    )) j := by
  sorry

/-- The chain map `NL_{B/A}^∧ ⊗_B C ⟶ NL_{C/A}^∧` induced by `toComp`. -/
@[no_expose] def toCompChainMap :
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
  comm' := toCompChainMap_comm I P Q

/-- Projection onto the relative variables commutes with the completed Jacobians. -/
private theorem ofCompChainMap_comm (i j : ℕ) (h : (ComplexShape.down ℕ).Rel i j) :
    (fun n : ℕ ↦ (show (naiveCotangent I (Q.comp P)).X n ⟶ (naiveCotangent (I.map (algebraMap A B)) Q).X n from
      match n with
    | 0 => ModuleCat.ofHom (ofCompOnVars (κ := κ) (ι := ι))
    | 1 => ModuleCat.ofHom (Cotangent.map (Presentation.ofCompHom Q P))
    | _ + 2 => 0
    )) i ≫ (naiveCotangent (I.map (algebraMap A B)) Q).d i j =
      (naiveCotangent I (Q.comp P)).d i j ≫ (fun n : ℕ ↦ (show (naiveCotangent I (Q.comp P)).X n ⟶ (naiveCotangent (I.map (algebraMap A B)) Q).X n from
      match n with
    | 0 => ModuleCat.ofHom (ofCompOnVars (κ := κ) (ι := ι))
    | 1 => ModuleCat.ofHom (Cotangent.map (Presentation.ofCompHom Q P))
    | _ + 2 => 0
    )) j := by
  sorry

/-- The chain map `NL_{C/A}^∧ ⟶ NL_{C/B}^∧` induced by `ofComp`. -/
@[no_expose] def ofCompChainMap :
    naiveCotangent I (Q.comp P) ⟶ naiveCotangent (I.map (algebraMap A B)) Q where
  f
    | 0 => ModuleCat.ofHom (ofCompOnVars (κ := κ) (ι := ι))
    | 1 => ModuleCat.ofHom (Cotangent.map (Presentation.ofCompHom Q P))
    | _ + 2 => 0
  comm' := ofCompChainMap_comm I P Q

/-- The scalar-extension adjunction unit is natural with respect to the complex differential. -/
private theorem unitChainMap_comm (i j : ℕ) (h : (ComplexShape.down ℕ).Rel i j) :
    (ModuleCat.extendRestrictScalarsAdj (algebraMap B C)).unit.app
        ((naiveCotangent I P).X i) ≫
      (((ModuleCat.restrictScalars (algebraMap B C)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (tensorComplex I P)).d i j =
    (naiveCotangent I P).d i j ≫
      (ModuleCat.extendRestrictScalarsAdj (algebraMap B C)).unit.app
        ((naiveCotangent I P).X j) := by
  sorry

/-- The unit of extension of scalars, as a chain map
`NL_{B/A}^∧ ⟶ restrict (NL_{B/A}^∧ ⊗_B C)`. -/
@[no_expose] def unitChainMap :
    naiveCotangent I P ⟶
      ((ModuleCat.restrictScalars (algebraMap B C)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj
        (tensorComplex I P) where
  f n := (ModuleCat.extendRestrictScalarsAdj (algebraMap B C)).unit.app
    ((naiveCotangent I P).X n)
  comm' := unitChainMap_comm I P

/-- The comparison `C ⊗[B] H^0(NL_{B/A}^∧) ⟶ H^0(NL_{B/A}^∧ ⊗_B C)`. -/
def homologyZero_tensor_to :
    ModuleCat.of C (C ⊗[B] ((naiveCotangent I P).homology 0 : Type u)) ⟶
      (tensorComplex I P).homology 0 :=
  (ModuleCat.ExtendScalars.tensorIso (R := B) (S := C)
      ((naiveCotangent I P).homology 0)).inv ≫
    ((ModuleCat.extendRestrictScalarsAdj (algebraMap B C)).homEquiv _ _).symm
      (HomologicalComplex.homologyMap (unitChainMap I P) 0 ≫
        (ModuleCat.restrictScalarsHomologyIso (algebraMap B C) (tensorComplex I P) 0).hom)

/-- The tensor of the degree-zero homology quotient annihilates the tensor differential. -/
private theorem homologyZero_tensor_from_condition :
    (tensorComplex I P).d 1 0 ≫
      ((ModuleCat.extendScalars (algebraMap B C)).map
          ((naiveCotangent I P).pOpcycles 0 ≫
            (naiveCotangent I P).isoHomologyι₀.inv) ≫
        (ModuleCat.ExtendScalars.tensorIso (R := B) (S := C)
            ((naiveCotangent I P).homology 0)).hom) = 0 := by
  sorry

/-- The comparison `H^0(NL_{B/A}^∧ ⊗_B C) ⟶ C ⊗[B] H^0(NL_{B/A}^∧)` induced by
right exactness of extension of scalars. -/
@[no_expose] def homologyZero_tensor_from :
    (tensorComplex I P).homology 0 ⟶
      ModuleCat.of C (C ⊗[B] ((naiveCotangent I P).homology 0 : Type u)) :=
  (tensorComplex I P).isoHomologyι₀.hom ≫
    (tensorComplex I P).descOpcycles
      ((ModuleCat.extendScalars (algebraMap B C)).map
          ((naiveCotangent I P).pOpcycles 0 ≫
            (naiveCotangent I P).isoHomologyι₀.inv) ≫
        (ModuleCat.ExtendScalars.tensorIso (R := B) (S := C)
            ((naiveCotangent I P).homology 0)).hom)
      1 (ChainComplex.prev ℕ 0) (homologyZero_tensor_from_condition I P)

/-- The homology-to-tensor comparison followed by its reverse is the identity. -/
private theorem homologyZero_tensor_hom_inv_id :
    homologyZero_tensor_from (C := C) I P ≫ homologyZero_tensor_to I P = 𝟙 _ := by
  sorry

/-- The tensor-to-homology comparison followed by its reverse is the identity. -/
private theorem homologyZero_tensor_inv_hom_id :
    homologyZero_tensor_to (C := C) I P ≫ homologyZero_tensor_from I P = 𝟙 _ := by
  sorry

/-- Right exactness of `C ⊗[B] -` identifies `H^0(NL_{B/A}^∧ ⊗_B C)` with
`C ⊗[B] H^0(NL_{B/A}^∧)`. Both directions are the explicit cokernel comparisons. -/
@[no_expose] def homologyZero_tensor_iso :
    (tensorComplex I P).homology 0 ≅
      ModuleCat.of C (C ⊗[B] ((naiveCotangent I P).homology 0 : Type u)) where
  hom := homologyZero_tensor_from I P
  inv := homologyZero_tensor_to I P
  hom_inv_id := homologyZero_tensor_hom_inv_id I P
  inv_hom_id := homologyZero_tensor_inv_hom_id I P

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

/-- The quotient map `⊕ᵢ B dx_i ⟶ H^0(NL_{B/A}^∧)`. -/
def homologyZeroπ :
    ((naiveCotangent I P).X 0 : Type u) →ₗ[B]
      ((naiveCotangent I P).homology 0 : Type u) :=
  ((naiveCotangent I P).pOpcycles 0 ≫ (naiveCotangent I P).isoHomologyι₀.inv).hom

/-- The conormal map from a composite presentation to the relative presentation is surjective. -/
theorem ofCompCotangentMap_surjective :
    Function.Surjective (Cotangent.map (Presentation.ofCompHom Q P)) := by
  sorry

/-- After scalar extension, inclusion of the old free differential generators is injective. -/
theorem toCompOnVars_liftBaseChange_injective :
    Function.Injective ((toCompOnVars (B := B) (C := C) (κ := κ) (ι := ι)).liftBaseChange C) := by
  sorry

/-- Lift a homology class to the composite conormal module, differentiate it,
retract to the old generators, and take the degree-zero homology class. -/
private def δValue
    (x : (naiveCotangent (I.map (algebraMap A B)) Q).homology 1) :
    C ⊗[B] ((naiveCotangent I P).homology 0 : Type u) :=
  (homologyZeroπ I P).baseChange C
    (Function.invFun ⇑((toCompOnVars (κ := κ) (ι := ι)).liftBaseChange C)
      (jacobian (Q.comp P)
        (Function.invFun ⇑(Cotangent.map (Presentation.ofCompHom Q P))
          (((naiveCotangent (I.map (algebraMap A B)) Q).iCycles 1).hom
            (Function.invFun
              (fun y ↦ ((naiveCotangent (I.map (algebraMap A B)) Q).homologyπ 1).hom y)
              x)))))

/-- Lifting, differentiating, and taking a homology class preserves addition. -/
private theorem δValue_map_add
    (x y : (naiveCotangent (I.map (algebraMap A B)) Q).homology 1) :
    δValue I P Q (x + y) = δValue I P Q x + δValue I P Q y := by
  sorry

/-- Lifting, differentiating, and taking a homology class commutes with scalars. -/
private theorem δValue_map_smul (c : C)
    (x : (naiveCotangent (I.map (algebraMap A B)) Q).homology 1) :
    δValue I P Q (c • x) = c • δValue I P Q x := by
  sorry

/-- The snake connecting map from relative degree-one homology to the scalar
extension of degree-zero homology over the original base. -/
@[no_expose] def δ :
    (naiveCotangent (I.map (algebraMap A B)) Q).homology 1 ⟶
      ModuleCat.of C (C ⊗[B] ((naiveCotangent I P).homology 0 : Type u)) :=
  ModuleCat.ofHom
    { toFun := δValue I P Q
      map_add' := δValue_map_add I P Q
      map_smul' := δValue_map_smul I P Q }

/-- The connecting map is computed by any conormal lift of a cycle and any
old-generator lift of its completed Jacobian. -/
theorem δ_lift
    (x : (naiveCotangent (I.map (algebraMap A B)) Q).cycles 1)
    (y : (Q.comp P).toExtension.Cotangent)
    (w : C ⊗[B] (ι → B))
    (hy : Cotangent.map (Presentation.ofCompHom Q P) y =
      ((naiveCotangent (I.map (algebraMap A B)) Q).iCycles 1).hom x)
    (hw : ((toCompOnVars (κ := κ) (ι := ι)).liftBaseChange C) w =
      jacobian (Q.comp P) y) :
    δ I P Q (((naiveCotangent (I.map (algebraMap A B)) Q).homologyπ 1).hom x) =
      (homologyZeroπ I P).baseChange C w := by
  sorry

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

/-- The unit chain map in each degree is the adjunction unit. -/
theorem unitChainMap_f (n : ℕ) :
    (unitChainMap I P).f n =
      (ModuleCat.extendRestrictScalarsAdj (algebraMap B C)).unit.app
        ((naiveCotangent I P).X n) := by
  rfl

include hB

/-- exactness of the six-term sequence at
`H^{-1}(NL_{C/B}^∧)`. -/
theorem exact_map_δ :
    Function.Exact (homologyOneMap I P Q) (δ I P Q) := sorry

/-- exactness of the six-term sequence at
`C ⊗_B H^0(NL_{B/A}^∧)`. -/
theorem exact_δ_homologyZeroBaseChange :
    Function.Exact (δ I P Q) (homologyZeroBaseChange I P Q) := sorry

/-- exactness of the six-term sequence at
`H^0(NL_{C/A}^∧)`. -/
theorem exact_homologyZeroBaseChange_map :
    Function.Exact (homologyZeroBaseChange I P Q) (homologyZeroMap I P Q) := sorry

/-- the terminal map `H^0(NL_{C/A}^∧) ⟶ H^0(NL_{C/B}^∧)` is
surjective. -/
theorem homologyZeroMap_surjective :
    Function.Surjective (homologyZeroMap I P Q) := sorry

/-- exactness of the six-term sequence at
`H^{-1}(NL_{C/A}^∧)`. -/
theorem exact_homologyOneTensor_map :
    Function.Exact (homologyOneTensor I P Q) (homologyOneMap I P Q) := sorry

/-- The connecting map vanishes on the image of the degree-one comparison. -/
theorem homologyOneMap_comp_δ :
    homologyOneMap I P Q ≫ δ I P Q = 0 := by
  ext x
  exact (exact_map_δ I P Q).apply_apply_eq_zero x

/-- The completed naive cotangent complexes of a tower have an exact six-term
Jacobi–Zariski sequence, ending in a surjective degree-zero map. -/
theorem jacobiZariski_exact :
    Function.Exact (homologyOneTensor I P Q) (homologyOneMap I P Q) ∧
    Function.Exact (homologyOneMap I P Q) (δ I P Q) ∧
    Function.Exact (δ I P Q) (homologyZeroBaseChange I P Q) ∧
    Function.Exact (homologyZeroBaseChange I P Q) (homologyZeroMap I P Q) ∧
    Function.Surjective (homologyZeroMap I P Q) :=
  ⟨exact_homologyOneTensor_map I P Q, exact_map_δ I P Q,
    exact_δ_homologyZeroBaseChange I P Q, exact_homologyZeroBaseChange_map I P Q,
    homologyZeroMap_surjective I P Q⟩

end Algebra.NaiveCotangent.Adic
