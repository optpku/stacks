module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Endomorphism
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Opposite

/-!
# Right Actions and Opposite Endomorphism Actions

This leaf identifies right differential graded module structures on fixed data with left
endomorphism actions of the Koszul opposite algebra.  The right-module owner remains the
canonical `DifferentialGradedModule`; handedness is changed only at this API boundary.
-/

@[expose] public section

noncomputable section

universe u v

variable {R : Type u} [CommRing R]

namespace DifferentialGradedModule

/-- A genuine right action of `A` on a cochain complex, represented canonically as a left
action of the Koszul opposite DGA on its endomorphism DGA. -/
@[stacks 0FQ5 "right differential graded action on a cochain complex"]
abbrev ActionOn (A : CochainDGAlgebra.{u, v} R)
    (K : CochainComplex (ModuleCat.{v} R) ℤ) :=
  LeftDifferentialGradedModule.ActionOn A.opposite K

/-- A right differential graded `A`-module with fixed graded pieces `M` and differential `dM`. -/
@[stacks 0FQ5]
structure WithFixedUnderlying (A : CochainDGAlgebra R) (M : ℤ → ModuleCat.{v} R)
    (dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)) where
  /-- The underlying canonical right differential graded module. -/
  toRightDifferentialGradedModule : DifferentialGradedModule A
  /-- Its graded pieces are the fixed family `M`. -/
  X_eq : toRightDifferentialGradedModule.X = M
  /-- Its differential is `dM` after transport along `X_eq`. -/
  d_eq : X_eq ▸ toRightDifferentialGradedModule.d = dM

namespace WithFixedUnderlying

variable {A : CochainDGAlgebra R} {M : ℤ → ModuleCat.{v} R}
  {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)}

/-- The fixed-underlying fiber coerces to its canonical right differential graded module. -/
instance : CoeOut (WithFixedUnderlying A M dM) (DifferentialGradedModule A) where
  coe N := N.toRightDifferentialGradedModule

/-- The right action transported to the fixed graded pieces. -/
def smul (N : WithFixedUnderlying A M dM) (p i : ℤ) :
    M p →ₗ[R] A.X i →ₗ[R] M (p + i) :=
  N.X_eq ▸ N.toRightDifferentialGradedModule.smul p i

/-- A fixed-underlying right module evaluates on homogeneous module and algebra elements. -/
instance : CoeFun (WithFixedUnderlying A M dM)
    (fun _ ↦ ∀ p i : ℤ, M p → A.X i → M (p + i)) where
  coe N := fun p i x a ↦ N.smul p i x a

/-- Coercion to a function is evaluation of the transported right action. -/
@[simp] theorem coe_apply (N : WithFixedUnderlying A M dM)
    (p i : ℤ) (x : M p) (a : A.X i) : N p i x a = N.smul p i x a := sorry

/-- The value of the opposite endomorphism action extracted from a fixed right module. -/
def toEndomorphismValue (N : WithFixedUnderlying A M dM)
    (i : ℤ) (a : A.X i) (p : ℤ) (x : M p) : M (i + p) :=
  (CochainDGAlgebra.oppositeSign R i p) •
    cast (congrArg (fun n : ℤ ↦ (M n : Type v)) (Int.add_comm p i)) (N.smul p i x a)

/-- Turn a fixed right action into a left action of the Koszul opposite algebra on endomorphisms. -/
def toEndomorphismDGAHom (N : WithFixedUnderlying A M dM) :
    EndomorphismDGAHom A.opposite M dM where
  map i :=
    { toFun := fun a p ↦
          { toFun := (toEndomorphismValue N i a p)
            map_add' := sorry
            map_smul' := sorry }
      map_add' := sorry
      map_smul' := sorry }
  d_sq := sorry
  map_one := sorry
  map_mul := sorry
  comm_d := sorry

/-- Evaluating the opposite endomorphism action gives the signed transported right action. -/
@[simp] theorem toEndomorphismDGAHom_apply (N : WithFixedUnderlying A M dM)
    (i : ℤ) (a : A.X i) (p : ℤ) (x : M p) :
    N.toEndomorphismDGAHom i a p x = toEndomorphismValue N i a p x := sorry

/-- The value of the right action recovered from an opposite endomorphism action. -/
def ofEndomorphismValue (tau : EndomorphismDGAHom A.opposite M dM)
    (p i : ℤ) (x : M p) (a : A.X i) : M (p + i) :=
  cast (congrArg (fun n : ℤ ↦ (M n : Type v)) (Int.add_comm i p))
    ((CochainDGAlgebra.oppositeSign R i p) • tau i a p x)

/-- Package an opposite endomorphism action as a right differential graded module on the fixed
graded pieces and differential. -/
def ofEndomorphismDGAHom (tau : EndomorphismDGAHom A.opposite M dM) :
    WithFixedUnderlying A M dM :=
  ⟨{ X := M
     d := dM
     smul p i :=
       { toFun := fun x ↦
           { toFun := (ofEndomorphismValue tau p i x)
             map_add' := sorry
             map_smul' := sorry }
         map_add' := sorry
         map_smul' := sorry }
     d_sq := tau.d_sq
     smul_one := sorry
     smul_mul := sorry
     comm_d := sorry },
   rfl, rfl⟩

/-- The right action packaged from an opposite endomorphism action is its signed transport. -/
@[simp] theorem ofEndomorphismDGAHom_apply (tau : EndomorphismDGAHom A.opposite M dM)
    (p i : ℤ) (x : M p) (a : A.X i) :
    ofEndomorphismDGAHom tau p i x a = ofEndomorphismValue tau p i x a := sorry

/-- Fixed-underlying right differential graded module structures are equivalent to their
degreewise endomorphism actions of the Koszul opposite algebra `A.opposite`. -/
def equivEndomorphismDGAHom (A : CochainDGAlgebra R) (M : ℤ → ModuleCat.{v} R)
    (dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)) :
    WithFixedUnderlying A M dM ≃ EndomorphismDGAHom A.opposite M dM where
  toFun := toEndomorphismDGAHom
  invFun := ofEndomorphismDGAHom
  left_inv := sorry
  right_inv := sorry

/-- Lemma 22.13.3: right differential graded `A`-module structures on a fixed cochain complex
`K` are equivalent to genuine DGA morphisms from `A.opposite` to the endomorphism DGA of `K`. -/
@[stacks 0FQ5]
def equivActionOn (A : CochainDGAlgebra.{u, v} R)
    (K : CochainComplex (ModuleCat.{v} R) ℤ) :
    WithFixedUnderlying A (fun n ↦ K.X n) (fun n ↦ (K.d n (n + 1)).hom) ≃
      LeftDifferentialGradedModule.ActionOn A.opposite K :=
  (equivEndomorphismDGAHom A (fun n ↦ K.X n) (fun n ↦ (K.d n (n + 1)).hom)).trans
    (EndomorphismDGAHom.equivActionOn A.opposite K)

/-- The canonical fixed-complex equivalence sends a right module structure to its genuine
opposite-algebra endomorphism-DGA morphism. -/
@[simp] theorem equivActionOn_apply
    {A : CochainDGAlgebra.{u, v} R} {K : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : WithFixedUnderlying A (fun n ↦ K.X n) (fun n ↦ (K.d n (n + 1)).hom)) :
    equivActionOn A K N = N.toEndomorphismDGAHom.toActionOn := sorry

/-- The forward equivalence map is the opposite endomorphism action of the right module. -/
@[simp] theorem equivEndomorphismDGAHom_apply (N : WithFixedUnderlying A M dM) :
    equivEndomorphismDGAHom A M dM N = N.toEndomorphismDGAHom := sorry

/-- The inverse equivalence map packages an opposite endomorphism action as a right module. -/
@[simp] theorem equivEndomorphismDGAHom_symm_apply
    (tau : EndomorphismDGAHom A.opposite M dM) :
    (equivEndomorphismDGAHom A M dM).symm tau = ofEndomorphismDGAHom tau := sorry

/-- Packaging an opposite endomorphism action and extracting it again is the identity. -/
@[simp] theorem toEndomorphismDGAHom_ofEndomorphismDGAHom
    (tau : EndomorphismDGAHom A.opposite M dM) :
    (ofEndomorphismDGAHom tau).toEndomorphismDGAHom = tau := sorry

/-- Extracting an opposite endomorphism action and packaging it again is the identity. -/
@[simp] theorem ofEndomorphismDGAHom_toEndomorphismDGAHom
    (N : WithFixedUnderlying A M dM) :
    ofEndomorphismDGAHom N.toEndomorphismDGAHom = N := sorry

/-- Extracting opposite endomorphism actions from fixed right modules is injective. -/
theorem toEndomorphismDGAHom_injective :
    Function.Injective
      (fun N : WithFixedUnderlying A M dM ↦ N.toEndomorphismDGAHom) := sorry

/-- Fixed-underlying right modules are determined by their homogeneous right actions. -/
@[ext] theorem ext {N₁ N₂ : WithFixedUnderlying A M dM}
    (h : ∀ (p i : ℤ) (x : M p) (a : A.X i), N₁ p i x a = N₂ p i x a) :
    N₁ = N₂ := sorry

/-- Extracting opposite endomorphism actions from fixed right modules is bijective. -/
theorem toEndomorphismDGAHom_bijective :
    Function.Bijective
      (fun N : WithFixedUnderlying A M dM ↦ N.toEndomorphismDGAHom) := sorry

end WithFixedUnderlying

/-- Recover the fixed-underlying right differential graded module from its genuine
opposite-algebra action on a bundled cochain complex. -/
def ActionOn.toFixed
    {A : CochainDGAlgebra.{u, v} R} {K : CochainComplex (ModuleCat.{v} R) ℤ}
    (rho : ActionOn A K) :
    WithFixedUnderlying A (fun n ↦ K.X n) (fun n ↦ (K.d n (n + 1)).hom) :=
  (WithFixedUnderlying.equivActionOn A K).symm rho

end DifferentialGradedModule
