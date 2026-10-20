/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.Topology.Sheaves.Sheaf
public import ReasLib.AlgebraicGeometry.AffineSpace.RegularFunctions
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open MvPolynomial

universe u v

section
variable {A B : Type u} [Category.{v} A] [Category.{v} B] (F : A ⥤ B) (G : B ⥤ A)

/- Companion definition (1): the left adjoint of a functor `F : A ⥤ B`. -/
#check (CategoryTheory.Adjunction G F : Type (max u v))

section
variable [F.IsRightAdjoint]

#check (CategoryTheory.Functor.leftAdjoint F : B ⥤ A)

#check (CategoryTheory.Adjunction.ofIsRightAdjoint F : F.leftAdjoint ⊣ F)

#check CategoryTheory.Adjunction.homEquiv (CategoryTheory.Adjunction.ofIsRightAdjoint F)

end

end

section
variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/- Companion definition (2): the transcendence degree of a field extension `L / K`. -/
#check (Algebra.trdeg K L : Cardinal)

#check IsTranscendenceBasis.cardinalMk_eq_trdeg

end

section
variable {k : Type u} [Field k] {n : ℕ} {X : Set (Fin n → k)} (φ : X → k)

/- Exercise 111.60.1 (Definitions) (3): a regular function on a classical affine variety
`X ⊂ k^n`. This is the main entry; the companion entries give the other five definitions. -/
@[stacks 0EEK] #check (MvPolynomial.IsRegular : (X → k) → Prop)

#check (MvPolynomial.regularFunctions X : Subalgebra k (X → k))

#check (MvPolynomial.mem_regularFunctions_iff :
  φ ∈ MvPolynomial.regularFunctions X ↔ MvPolynomial.IsRegular φ)

end

section
variable {C : Type u} [Category.{v} C] (X : TopCat.{u}) (F : TopCat.Presheaf C X)

/- Companion definition (4): a sheaf on a topological space. -/
#check (TopCat.Sheaf C X : Type (max u v))

#check (TopCat.Presheaf.IsSheaf F : Prop)

end

section
variable {R : Type u} [CommRing R]

/- Companion definition (5): a local ring. -/
#check (IsLocalRing R : Prop)

#check IsLocalRing.of_unique_max_ideal

section
variable [IsLocalRing R]

#check (IsLocalRing.maximal_ideal_unique R : ∃! I : Ideal R, I.IsMaximal)

end

end

section
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/- Companion definition (6): a morphism of schemes `f : X ⟶ Y` being affine. -/
#check (AlgebraicGeometry.IsAffineHom f : Prop)

#check (AlgebraicGeometry.isAffineHom_iff (f := f) :
  IsAffineHom f ↔ ∀ U : Y.Opens, IsAffineOpen U → IsAffineOpen (f ⁻¹ᵁ U))

end
