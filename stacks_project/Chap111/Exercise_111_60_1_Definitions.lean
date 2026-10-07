module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.Topology.Sheaves.Sheaf
public import stacks_project.Chap111.Exercise_111_31_5_Regular
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open MvPolynomial

universe u v

section
variable {A B : Type u} [Category.{v} A] [Category.{v} B] (F : A ⥤ B) [F.IsRightAdjoint]

/- Exercise 111.60.1 (Definitions) (1): the left adjoint of a functor `F : A ⥤ B`. -/
@[stacks 0EEK] #check (F.leftAdjoint : B ⥤ A)

#check Adjunction

#check (Adjunction.ofIsRightAdjoint F : F.leftAdjoint ⊣ F)

#check (Adjunction.ofIsRightAdjoint F).homEquiv

end

section
variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/- Exercise 111.60.1 (Definitions) (2): the transcendence degree of a field extension `L / K`. -/
@[stacks 0EEK] #check (Algebra.trdeg K L : Cardinal)

#check IsTranscendenceBasis.cardinalMk_eq_trdeg

end

section
variable {k : Type u} [Field k] {n : ℕ} {X : Set (Fin n → k)} (φ : X → k)

/- Exercise 111.60.1 (Definitions) (3): a regular function on a classical affine variety
`X ⊂ k^n`. -/
@[stacks 0EEK] #check (MvPolynomial.IsRegular φ : Prop)

#check (MvPolynomial.regularFunctions X : Subalgebra k (X → k))

#check (MvPolynomial.mem_regularFunctions_iff :
  φ ∈ MvPolynomial.regularFunctions X ↔ MvPolynomial.IsRegular φ)

end

section
variable {C : Type u} [Category.{v} C] (X : TopCat.{u}) (F : TopCat.Presheaf C X)

/- Exercise 111.60.1 (Definitions) (4): a sheaf on a topological space. -/
@[stacks 0EEK] #check (TopCat.Sheaf C X)

#check (F.IsSheaf : Prop)

end

section
variable {R : Type u} [CommRing R]

/- Exercise 111.60.1 (Definitions) (5): a local ring. -/
@[stacks 0EEK] #check (IsLocalRing R : Prop)

#check IsLocalRing.of_unique_max_ideal

section
variable [IsLocalRing R]

#check (IsLocalRing.maximal_ideal_unique R : ∃! I : Ideal R, I.IsMaximal)

end

end

section
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/- Exercise 111.60.1 (Definitions) (6): a morphism of schemes `f : X ⟶ Y` being affine. -/
@[stacks 0EEK] #check (IsAffineHom f : Prop)

#check (isAffineHom_iff (f := f) :
  IsAffineHom f ↔ ∀ U : Y.Opens, IsAffineOpen U → IsAffineOpen (f ⁻¹ᵁ U))

end
