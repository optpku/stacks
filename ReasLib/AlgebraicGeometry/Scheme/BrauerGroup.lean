module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Azumaya

/-!
# The Brauer group of a scheme

Classes of Azumaya `𝒪_S`-algebras up to tensoring with positive-rank internal
endomorphism algebras.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped CategoryTheory.MonObj
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-- Two monoid objects in `S.Modules` are Brauer equivalent when, after tensoring with internal
endomorphism algebras of finite locally free positive-rank modules, they become isomorphic as
monoid objects. -/
def IsBrauerEquivalent (A B : S.Modules) [MonObj A] [MonObj B] : Prop :=
  ∃ (F G : S.Modules) (_ : IsFiniteLocallyFree F) (_ : IsFiniteLocallyFree G),
    (∀ x : S, 0 < fiberFinrank F x) ∧
      (∀ x : S, 0 < fiberFinrank G x) ∧
        ∃ e : A ⊗ internalHom F F ≅ B ⊗ internalHom G G, IsMonHom e.hom

/-- Unfolding of Brauer equivalence into the two endomorphism factors and the algebra isomorphism. -/
theorem IsBrauerEquivalent.iff_exists_endomorphism (A B : S.Modules) [MonObj A] [MonObj B] :
    IsBrauerEquivalent A B ↔
      ∃ (F G : S.Modules) (_ : IsFiniteLocallyFree F) (_ : IsFiniteLocallyFree G),
        (∀ x : S, 0 < fiberFinrank F x) ∧
          (∀ x : S, 0 < fiberFinrank G x) ∧
            ∃ e : A ⊗ internalHom F F ≅ B ⊗ internalHom G G, IsMonHom e.hom := sorry

/-- Brauer equivalence is reflexive. -/
theorem IsBrauerEquivalent.refl (A : S.Modules) [MonObj A] :
    IsBrauerEquivalent A A := sorry

/-- Brauer equivalence is symmetric. -/
theorem IsBrauerEquivalent.symm {A B : S.Modules} [MonObj A] [MonObj B]
    (h : IsBrauerEquivalent A B) : IsBrauerEquivalent B A := sorry

/-- An Azumaya algebra object of a scheme is a bundled monoid object satisfying the
Azumaya condition. -/
def AzumayaObj (S : Scheme.{u}) :=
  {algebra : CategoryTheory.Mon S.Modules // IsAzumaya algebra.X}

/-- A scheme module with its given monoid and Azumaya structures defines a bundled
Azumaya algebra object. -/
def AzumayaObj.of (A : S.Modules) [hM : MonObj A] [hA : IsAzumaya A] : AzumayaObj S :=
  ⟨{ X := A, mon := hM }, hA⟩

/-- Tensor product of Azumaya algebra objects. -/
noncomputable def AzumayaObj.tensor (A B : AzumayaObj S) : AzumayaObj S :=
  ⟨A.val ⊗ B.val,
    @isAzumaya_tensor S A.val.X B.val.X A.val.mon B.val.mon A.property B.property⟩

/-- Opposite algebra structure on the same underlying module, using the tensor symmetry. -/
noncomputable def AzumayaObj.opposite (A : AzumayaObj S) : AzumayaObj S :=
  let algebra : CategoryTheory.Mon S.Modules :=
    { X := A.val.X
      mon :=
        { one := A.val.mon.one
          mul := (β_ A.val.X A.val.X).hom ≫ A.val.mon.mul
          one_mul := sorry
          mul_one := sorry
          mul_assoc := sorry } }
  ⟨algebra, (sorry : IsAzumaya algebra.X)⟩

/-- The tensor unit of scheme modules is finite locally free of positive fiber rank, so its
internal endomorphism algebra is Azumaya. -/
noncomputable def AzumayaObj.one (S : Scheme.{u}) : AzumayaObj S :=
  AzumayaObj.of (internalHom (𝟙_ S.Modules) (𝟙_ S.Modules))

/-- Setoid of Azumaya algebra objects by Brauer equivalence. -/
def brauerSetoid (S : Scheme.{u}) : Setoid (AzumayaObj S) where
  r A B := @IsBrauerEquivalent S A.val.X B.val.X A.val.mon B.val.mon
  iseqv := sorry

/-- The Brauer group of a scheme is the group of Brauer-equivalence classes of Azumaya
`𝒪_S`-algebras. -/
def BrauerGroup (S : Scheme.{u}) : Type (u + 1) :=
  Quotient (brauerSetoid S)

/-- Class of an Azumaya `𝒪_S`-algebra in the Brauer group. -/
noncomputable def classOf (A : S.Modules) [MonObj A] [IsAzumaya A] : BrauerGroup S :=
  Quotient.mk (brauerSetoid S) (AzumayaObj.of A)

/-- Classes in the Brauer group coincide if and only if the algebras are Brauer equivalent. -/
theorem classOf_eq_iff (A B : S.Modules) [MonObj A] [MonObj B] [IsAzumaya A] [IsAzumaya B] :
    classOf A = classOf B ↔ IsBrauerEquivalent A B := sorry

/-- The Brauer group of a scheme is an abelian group under tensor product of Azumaya algebras. -/
noncomputable instance instCommGroupBrauerGroup (S : Scheme.{u}) : CommGroup (BrauerGroup S) where
  mul :=
    Quotient.lift₂ (fun A B ↦ Quotient.mk (brauerSetoid S) (A.tensor B)) sorry
  one := Quotient.mk (brauerSetoid S) (AzumayaObj.one S)
  inv := Quotient.lift (fun A ↦ Quotient.mk (brauerSetoid S) A.opposite) sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry
  inv_mul_cancel := sorry
  mul_comm := sorry

/-- The Brauer class of the internal endomorphism algebra of a finite locally free
positive-rank module. -/
noncomputable def classOfEnd (F : S.Modules) [IsFiniteLocallyFree F]
    (hF : ∀ x : S, 0 < fiberFinrank F x) : BrauerGroup S :=
  @classOf S (internalHom F F) inferInstance (isAzumaya_internalHomEnd F hF)

/-- The class of an internal endomorphism algebra of a finite locally free positive-rank module
is trivial in the Brauer group. -/
theorem classOf_end_eq_one (F : S.Modules) [IsFiniteLocallyFree F]
    (hF : ∀ x : S, 0 < fiberFinrank F x) : classOfEnd F hF = 1 := sorry

/-- Tensor product of Azumaya algebras multiplies Brauer classes. -/
theorem classOf_tensor (A B : S.Modules) [MonObj A] [MonObj B] [IsAzumaya A] [IsAzumaya B] :
    classOf (A ⊗ B) = classOf A * classOf B := sorry

end AlgebraicGeometry.Scheme
