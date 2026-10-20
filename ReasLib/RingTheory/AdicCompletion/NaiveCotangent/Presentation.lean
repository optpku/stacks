module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.RingTheory.AdicCompletion.TopologicallyFiniteType.Tower
public import ReasLib.RingTheory.AdicCompletion.Polynomial.Evaluation

/-!
# Composite completed polynomial presentations

Given presentations `B = A[x_ι]^∧ / J` and `C = B[y_κ]^∧ / J'`, the composite
presentation is `C = A[x_ι, y_κ]^∧ / K`, together with the polynomial-ring
maps that form the columns of the Jacobi–Zariski snake diagram.
-/

@[expose] public section

noncomputable section

universe u

open Algebra.NaiveCotangent.Adic

namespace Algebra.NaiveCotangent.Adic

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}

/-- Completeness of `A[x_ι]^∧` along the extended ideal `I · A[x_ι]^∧`, so that
completed evaluation into a polynomial completion is defined. Finite generation
of `I` is used via `AdicCompletion.isAdicComplete`. -/
@[implicit_reducible] def polynomialCompletion_isAdicComplete_map (ι : Type u) :
    IsAdicComplete (I.map (algebraMap A (polynomialCompletion A I ι)))
      (polynomialCompletion A I ι) :=
  (IsAdicComplete.map_algebraMap_iff (R := A) (S := polynomialCompletion A I ι)
      (M := polynomialCompletion A I ι) I).mpr
    ((IsAdicComplete.map_algebraMap_iff (R := A) (S := MvPolynomial ι A)
        (M := polynomialCompletion A I ι) I).mp
      (AdicCompletion.isAdicComplete
        (Ideal.FG.map (IsNoetherian.noetherian I)
          (algebraMap A (MvPolynomial ι A)))))

variable {B : Type u} [CommRing B] [Algebra A B]

/-- Completeness of `B[y_κ]^∧` along the extended ideal of `I`, as an
`A`-algebra. Finite generation of `I B` follows from finite generation of `I`. -/
@[implicit_reducible] def polynomialCompletion_tower_isAdicComplete_map (ι : Type u) :
    IsAdicComplete
      (I.map (algebraMap A (polynomialCompletion B (I.map (algebraMap A B)) ι)))
      (polynomialCompletion B (I.map (algebraMap A B)) ι) :=
  (IsAdicComplete.map_algebraMap_iff (R := A)
      (S := polynomialCompletion B (I.map (algebraMap A B)) ι)
      (M := polynomialCompletion B (I.map (algebraMap A B)) ι) I).mpr
    ((IsAdicComplete.map_algebraMap_iff (R := A) (S := B)
        (M := polynomialCompletion B (I.map (algebraMap A B)) ι) I).mp
      ((IsAdicComplete.map_algebraMap_iff (R := B) (S := MvPolynomial ι B)
          (M := polynomialCompletion B (I.map (algebraMap A B)) ι)
          (I.map (algebraMap A B))).mp
        (AdicCompletion.isAdicComplete
          (Ideal.FG.map
            (Ideal.FG.map (IsNoetherian.noetherian I) (algebraMap A B))
            (algebraMap B (MvPolynomial ι B))))))

variable {C : Type u} [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
variable [Algebra.TopologicallyFiniteType I C]
variable {ι κ : Type u}

namespace Presentation

/-- Completed evaluation at the variables of two successive presentations. -/
def compToAlgHom (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (P : Presentation A B I ι) : polynomialCompletion A I (κ ⊕ ι) →ₐ[A] C :=
  adicAeval I (Sum.elim (fun j ↦ Q.toAlgHom (X (I.map (algebraMap A B)) j))
    (fun i ↦ algebraMap B C (P.toAlgHom (X I i))))

/-- Completed evaluation at two successive sets of presentation variables is surjective. -/
theorem compToAlgHom_surjective (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (P : Presentation A B I ι) : Function.Surjective (compToAlgHom Q P) := by
  sorry

/-- The composite completed polynomial presentation obtained from two successive presentations. -/
def comp (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (P : Presentation A B I ι) : Presentation A C I (κ ⊕ ι) where
  toAlgHom := compToAlgHom Q P
  surjective := compToAlgHom_surjective Q P

/-- The structure map of the composite presentation evaluates the `y`-variables
at the images of the `Q`-variables in `C`. -/
theorem comp_X_inl (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (P : Presentation A B I ι) (j : κ) :
    (comp Q P).toAlgHom (X I (Sum.inl j)) =
      Q.toAlgHom (X (I.map (algebraMap A B)) j) := by
  exact adicAeval_X I _ (Sum.inl j)

/-- The structure map of the composite presentation evaluates the `x`-variables
at the images of the `P`-variables in `C`. -/
theorem comp_X_inr (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (P : Presentation A B I ι) (i : ι) :
    (comp Q P).toAlgHom (X I (Sum.inr i)) = algebraMap B C (P.toAlgHom (X I i)) := by
  exact adicAeval_X I _ (Sum.inr i)

/-- The composite presentation is a surjective `A`-algebra map
`A[x_ι, y_κ]^∧ →ₐ[A] C`. -/
theorem comp_surjective (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (P : Presentation A B I ι) :
    Function.Surjective (comp Q P).toAlgHom :=
  (comp Q P).surjective

/-- The map of completed polynomial rings `A[x_ι]^∧ →ₐ[A] A[x_ι, y_κ]^∧` sending
`x_i` to the corresponding composite indeterminate. -/
def toComp (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (P : Presentation A B I ι) :
    polynomialCompletion A I ι →ₐ[A] polynomialCompletion A I (κ ⊕ ι) :=
  @adicAeval _ _ _ _ _ _ I (polynomialCompletion_isAdicComplete_map (I := I) (κ ⊕ ι))
    fun i ↦ X I (Sum.inr i)

/-- `toComp` sends the indeterminate `X I i` to `X I (Sum.inr i)`. -/
theorem toComp_X (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (P : Presentation A B I ι) (i : ι) :
    (toComp Q P) (X I i) = X I (Sum.inr i) := by
  exact @adicAeval_X _ _ _ _ _ _ I
    (polynomialCompletion_isAdicComplete_map (I := I) (κ ⊕ ι)) _ i

/-- The completed variable inclusion commutes with the presentation maps. -/
theorem toCompHom_over (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (P : Presentation A B I ι) (x : polynomialCompletion A I ι) :
    (comp Q P).toAlgHom (toComp Q P x) = algebraMap B C (P.toAlgHom x) := by
  sorry

/-- The morphism of `A`-extensions induced by `toComp`. -/
def toCompHom (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (P : Presentation A B I ι) :
    P.toExtension.Hom (comp Q P).toExtension where
  toRingHom := (toComp Q P).toRingHom
  toRingHom_algebraMap x := by
    change (toComp Q P) (algebraMap A (polynomialCompletion A I ι) x) =
      algebraMap A (polynomialCompletion A I (κ ⊕ ι)) (algebraMap A A x)
    exact (toComp Q P).commutes x
  algebraMap_toRingHom := toCompHom_over Q P

/-- The map of completed polynomial rings `A[x_ι, y_κ]^∧ →ₐ[A] B[y_κ]^∧` sending
`y_j` to the `B`-indeterminate and `x_i` to the image of the `P`-variable. -/
def ofComp (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (P : Presentation A B I ι) :
    polynomialCompletion A I (κ ⊕ ι) →ₐ[A]
      polynomialCompletion B (I.map (algebraMap A B)) κ :=
  @adicAeval _ _ _ _ _ _ I
    (polynomialCompletion_tower_isAdicComplete_map (I := I) (B := B) κ)
    (Sum.elim (X (I.map (algebraMap A B)))
    (fun i ↦ algebraMap B (polynomialCompletion B (I.map (algebraMap A B)) κ)
      (P.toAlgHom (X I i))))

/-- `ofComp` sends a `y`-indeterminate to the corresponding `B[y_κ]^∧`
indeterminate. -/
theorem ofComp_X_inl (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (P : Presentation A B I ι) (j : κ) :
    (ofComp Q P) (X I (Sum.inl j)) = X (I.map (algebraMap A B)) j := by
  exact @adicAeval_X _ _ _ _ _ _ I
    (polynomialCompletion_tower_isAdicComplete_map (I := I) (B := B) κ) _ (Sum.inl j)

/-- `ofComp` sends an `x`-indeterminate to the constant given by the image of
the corresponding `P`-variable. -/
theorem ofComp_X_inr (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (P : Presentation A B I ι) (i : ι) :
    (ofComp Q P) (X I (Sum.inr i)) =
      algebraMap B (polynomialCompletion B (I.map (algebraMap A B)) κ)
        (P.toAlgHom (X I i)) := by
  exact @adicAeval_X _ _ _ _ _ _ I
    (polynomialCompletion_tower_isAdicComplete_map (I := I) (B := B) κ) _ (Sum.inr i)

/-- Completed evaluation into the intermediate-base presentation commutes with its quotient map. -/
theorem ofCompHom_over (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (P : Presentation A B I ι) (x : polynomialCompletion A I (κ ⊕ ι)) :
    Q.toAlgHom (ofComp Q P x) = (comp Q P).toAlgHom x := by
  sorry

/-- The morphism of extensions induced by `ofComp`. -/
def ofCompHom (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (P : Presentation A B I ι) :
    (comp Q P).toExtension.Hom Q.toExtension where
  toRingHom := (ofComp Q P).toRingHom
  toRingHom_algebraMap x := by
    change (ofComp Q P) (algebraMap A (polynomialCompletion A I (κ ⊕ ι)) x) =
      algebraMap B (polynomialCompletion B (I.map (algebraMap A B)) κ) (algebraMap A B x)
    rw [← IsScalarTower.algebraMap_apply]
    exact (ofComp Q P).commutes x
  algebraMap_toRingHom x := ofCompHom_over Q P x

end Presentation

end Algebra.NaiveCotangent.Adic
