/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Noetherian.Ideal
public import ReasLib.AlgebraicGeometry.Scheme.Noetherian.Characterization
public import ReasLib.RingTheory.RingHom.Finite.Generators
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Finite.Cover
public import ReasLib.RingTheory.KrullDimension.Chains
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry BigOperators

universe u v

variable {R A : Type u} {B : Type v} [CommRing R] [CommRing A] [CommRing B]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (φ : A →+* B)

/- Exercise 111.55.1 (Definitions) (1): a Noetherian ring. -/
@[stacks 07DF] #check (isNoetherianRing_iff_exists_finset_span R :
  IsNoetherianRing R ↔
    ∀ ideal : Ideal R, ∃ generators : Finset R, Ideal.span (generators : Set R) = ideal)

#check (IsNoetherianRing R : Prop)

#check (isNoetherianRing_iff_ideal_fg R :
  IsNoetherianRing R ↔ ∀ I : Ideal R, I.FG)

/- Exercise 111.55.1 (Definitions) (2): a Noetherian scheme. -/
@[stacks 07DF] #check (AlgebraicGeometry.isNoetherian_iff_compactSpace_and_affineSections X :
  IsNoetherian X ↔ CompactSpace X ∧ ∀ U : X.affineOpens, IsNoetherianRing Γ(X, U))

#check (IsNoetherian X : Prop)

#check (isNoetherian_iff (X := X) :
  IsNoetherian X ↔ IsLocallyNoetherian X ∧ CompactSpace X)

/- Exercise 111.55.1 (Definitions) (3): a finite ring homomorphism. -/
@[stacks 07DF] #check (RingHom.finite_iff_exists_generators φ :
  φ.Finite ↔ ∃ (n : ℕ) (generators : Fin n → B),
    ∀ value : B, ∃ coefficients : Fin n → A,
      value = ∑ index, φ (coefficients index) * generators index)

#check (φ.Finite : Prop)

#check (RingHom.finite_algebraMap :
  ∀ {A : Type u} {B : Type u} [CommRing A] [CommRing B] [Algebra A B],
    (algebraMap A B).Finite ↔ Module.Finite A B)

/- Exercise 111.55.1 (Definitions) (4): a finite morphism of schemes. -/
@[stacks 07DF] #check (AlgebraicGeometry.isFinite_iff_exists_affineOpenCover f :
  IsFinite f ↔
    ∃ 𝒰 : Y.AffineOpenCover.{u},
      ∀ i : 𝒰.I₀,
        IsAffine (f ⁻¹ᵁ (𝒰.f i).opensRange) ∧
          (CommRingCat.Hom.hom
            (Scheme.Hom.appTop (f ∣_ (𝒰.f i).opensRange))).Finite)

#check (IsFinite f : Prop)

#check (isFinite_iff f :
  IsFinite f ↔
    IsAffineHom f ∧
      ∀ U : Y.Opens, IsAffineOpen U → (f.app U).hom.Finite)

/- Exercise 111.55.1 (Definitions) (5): the dimension of a ring. -/
@[stacks 07DF] #check (ringKrullDim_eq_iSup_chainLength R :
  ringKrullDim R = ⨆ chain : LTSeries (PrimeSpectrum R), (chain.length : WithBot ℕ∞))

#check (ringKrullDim R : WithBot ℕ∞)
