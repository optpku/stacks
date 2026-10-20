module

public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.BaseChange.Obstruction
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

open CategoryTheory DerivedCategory HomologicalComplex ComplexShape
open CategoryTheory.Pretriangulated
open Algebra Algebra.Generators Algebra.Extension
open Algebra.Extension.NaiveCotangent
open Algebra.NaiveCotangent.DerivedBaseChange
open RingHom.SquareZeroExtension
open scoped DerivedExt NaiveCotangent DerivedTensorWithAlgebra

/- Remark 91.2.8 (1) In the situation of Lemma 91.2.7, Ext¹_A(NL{A⁄A'}, N) is identified with the derived base-change Ext¹. -/
@[stacks 0GPY] #check (RingHom.SquareZeroExtension.extOne_adjunction :
  ∀ {A' A : Type u} [CommRing A'] [CommRing A]
    (π : A' →+* A) [π.IsSquareZeroExtension]
    (B : Type u) [CommRing B] [Algebra A B]
    {N : Type u} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N],
    -- Local instance justification (noncanonical choice): the naive cotangent object uses the A'-algebra structure on A selected by the explicit π.
    letI := RingHom.SquareZeroExtension.algebraOfSquareZero π
    Ext⁽(1 : ℤ)⁾(Algebra.naiveCotangentObject A' A,
        (ModuleCat.derivedRestrictionOfScalars (algebraMap A B)).obj
          ((singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B N))) ≃+
      Ext⁽(1 : ℤ)⁾(Algebra.naiveCotangentObject A' A ⊗[A]^L[B],
        (singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B N)))

/- Remark 91.2.8 (2) The derived base-change Ext¹ equals Ext¹ of the underived tensor `NL{A⁄A'} ⊗[A] B`. -/
@[stacks 0GPY] #check (RingHom.SquareZeroExtension.extOne_underived :
  ∀ {A' A : Type u} [CommRing A'] [CommRing A]
    (π : A' →+* A) [π.IsSquareZeroExtension]
    (B : Type u) [CommRing B] [Algebra A B]
    {N : Type u} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N],
    -- Local instance justification (noncanonical choice): the base-change Ext¹ groups use the A'-algebra structure on A selected by the explicit π.
    letI := RingHom.SquareZeroExtension.algebraOfSquareZero π
    Function.Bijective
      (RingHom.SquareZeroExtension.extOne_underived_precomp π B :
        Ext⁽(1 : ℤ)⁾(RingHom.SquareZeroExtension.underivedTensorObject π B,
            (singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B N)) →
          Ext⁽(1 : ℤ)⁾(Algebra.naiveCotangentObject A' A ⊗[A]^L[B],
            (singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B N))))

/- Remark 91.2.8 (3) There is a canonical map of complexes `NL{A⁄A'} ⊗[A] B ⟶ NL{B⁄A'}`. -/
@[stacks 0GPY] #check (RingHom.SquareZeroExtension.baseChangeMap :
  ∀ {A' A : Type u} [CommRing A'] [CommRing A]
    (π : A' →+* A)
    (B : Type u) [CommRing B] [Algebra A B],
    -- Local instance justification (noncanonical choice): the source self-presentation uses the A'-algebra structure on A selected by the explicit π.
    letI := RingHom.SquareZeroExtension.algebraOfSquareZero π
    -- Local instance justification (noncanonical choice): the target self-presentation uses the composite of π and algebraMap A B as its A'-algebra structure.
    letI := RingHom.SquareZeroExtension.algebraCompOfSquareZero π B
    -- Local instance justification (defeq pin): the tower is the composite of the two explicitly selected algebra maps.
    letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
    NaiveCotangent.BaseChange.tensorModel (Generators.self A' A).toExtension ⟶
      Algebra.naiveCotangent A' B)

/- Remark 91.2.8 (4) There is a canonical map of complexes `NL{B⁄A'} ⟶ NL{B⁄A}`. -/
@[stacks 0GPY] #check (RingHom.SquareZeroExtension.sourceChangeMap :
  ∀ {A' A : Type u} [CommRing A'] [CommRing A]
    (π : A' →+* A)
    (B : Type u) [CommRing B] [Algebra A B],
    -- Local instance justification (noncanonical choice): the change-of-base-ring map uses the A'-algebra structure on A selected by the explicit π.
    letI := RingHom.SquareZeroExtension.algebraOfSquareZero π
    -- Local instance justification (noncanonical choice): the source self-presentation uses the composite of π and algebraMap A B as its A'-algebra structure.
    letI := RingHom.SquareZeroExtension.algebraCompOfSquareZero π B
    -- Local instance justification (defeq pin): the tower is the composite of the two explicitly selected algebra maps.
    letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
    Algebra.naiveCotangent A' B ⟶ Algebra.naiveCotangent A B)

/- Remark 91.2.8 (5) If these maps complete to a distinguished triangle, the connecting image of ξ is the obstruction to a solution of 91.2.0.1. -/
@[stacks 0GPY] #check (RingHom.SquareZeroExtension.exists_iff_connecting_eq_zero :
  ∀ {A' A : Type u} [CommRing A'] [CommRing A]
    (π : A' →+* A) [π.IsSquareZeroExtension]
    (B : Type u) [CommRing B] [Algebra A B]
    {N : Type u} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (c : RingHom.SquareZeroExtension.KernelModule π →ₗ[A] N)
    (γ :
      -- Local instance justification (noncanonical choice): the tensor object uses the A'-algebra structure on A selected by the explicit π.
      letI := RingHom.SquareZeroExtension.algebraOfSquareZero π
      Algebra.naiveCotangentObject A B ⟶
        (RingHom.SquareZeroExtension.underivedTensorObject π B)⟦(1 : ℤ)⟧)
    (hΔ :
      -- Local instance justification (noncanonical choice): the first triangle object uses the A'-algebra structure on A selected by the explicit π.
      letI := RingHom.SquareZeroExtension.algebraOfSquareZero π
      -- Local instance justification (noncanonical choice): the middle triangle object uses the composite of π and algebraMap A B as its A'-algebra structure.
      letI := RingHom.SquareZeroExtension.algebraCompOfSquareZero π B
      -- Local instance justification (defeq pin): the triangle maps use the tower of the two explicitly selected algebra maps.
      letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
      Triangle.mk
          (RingHom.SquareZeroExtension.baseChangeMapDerived π B)
          (RingHom.SquareZeroExtension.sourceChangeMapDerived π B) γ ∈
        distTriang (DerivedCategory (ModuleCat B))),
    -- Local instance justification (noncanonical choice): the representative and Ext¹ groups use the A'-algebra structure on A selected by the explicit π.
    letI := RingHom.SquareZeroExtension.algebraOfSquareZero π
    Nonempty (RingHom.SquareZeroExtension.IsoClass π B c) ↔
      ∃ (f :
          -- Local instance justification (noncanonical choice): the conormal representative uses the self-presentation for the A'-algebra structure selected by π.
          letI := RingHom.SquareZeroExtension.algebraOfSquareZero π
          (Generators.self A' A).toExtension.Cotangent →ₗ[A] N)
        (ξu :
          -- Local instance justification (noncanonical choice): the underived tensor object uses the A'-algebra structure on A selected by the explicit π.
          letI := RingHom.SquareZeroExtension.algebraOfSquareZero π
          Ext⁽(1 : ℤ)⁾(RingHom.SquareZeroExtension.underivedTensorObject π B,
            (singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B N))),
        (
          -- Local instance justification (noncanonical choice): the extension class and its representative use the A'-algebra structure on A selected by π.
          letI := RingHom.SquareZeroExtension.algebraOfSquareZero π
          extOneNaiveCotangent_mk A' A N f =
            extOneNaiveCotangent_map c
              (RingHom.SquareZeroExtension.selfExtensionClass π)) ∧
        (
          -- Local instance justification (noncanonical choice): the derived Ext¹ comparison uses the A'-algebra structure on A selected by π.
          letI := RingHom.SquareZeroExtension.algebraOfSquareZero π
          RingHom.SquareZeroExtension.extOne_underived_precomp π B ξu =
            RingHom.SquareZeroExtension.extOne_adjunction π B
              (RingHom.SquareZeroExtension.toDerived π B f)) ∧
        (
          -- Local instance justification (noncanonical choice): uniqueness is in the Ext¹ group for the A'-algebra structure on A selected by π.
          letI := RingHom.SquareZeroExtension.algebraOfSquareZero π
          ∀ ξu',
            RingHom.SquareZeroExtension.extOne_underived_precomp π B ξu' =
                RingHom.SquareZeroExtension.extOne_adjunction π B
                  (RingHom.SquareZeroExtension.toDerived π B f) →
              ξu' = ξu) ∧
        RingHom.SquareZeroExtension.connectingExtTwo π B γ ξu = 0)
