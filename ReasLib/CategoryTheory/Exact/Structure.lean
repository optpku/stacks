/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Exact Structures

This file packages an exact structure by its admissible kernel-cokernel pairs.  Its ambient
category is additive in the standard mathlib sense: it is preadditive and has finite products
(hence finite biproducts).
-/

open CategoryTheory Limits

universe u v

namespace CategoryTheory

/-- A short complex is a kernel-cokernel pair when its first map is a kernel of its second map and
its second map is a cokernel of its first map. -/
@[stacks 05SF "kernel-cokernel pair"]
def IsKernelCokernelPair
    {A : Type u} [Category.{v} A] [Preadditive A] (S : ShortComplex A) : Prop :=
  Nonempty (IsLimit (KernelFork.ofι S.f S.zero)) ∧
    Nonempty (IsColimit (CokernelCofork.ofπ S.g S.zero))

/-- A morphism is admissible monic for a class of short complexes when it occurs as the first map
of a complex in that class. -/
@[stacks 05SF "admissible monomorphism"]
def IsAdmissibleMono
    {A : Type u} [Category.{v} A] [Preadditive A]
    (admissible : Set (ShortComplex A)) {X Y : A} (i : X ⟶ Y) : Prop :=
  ∃ (Z : A) (p : Y ⟶ Z) (w : i ≫ p = 0), admissible (ShortComplex.mk i p w)

/-- A morphism is admissible epic for a class of short complexes when it occurs as the second map
of a complex in that class. -/
@[stacks 05SF "admissible epimorphism"]
def IsAdmissibleEpi
    {A : Type u} [Category.{v} A] [Preadditive A]
    (admissible : Set (ShortComplex A)) {Y Z : A} (p : Y ⟶ Z) : Prop :=
  ∃ (X : A) (i : X ⟶ Y) (w : i ≫ p = 0), admissible (ShortComplex.mk i p w)

/-- An exact structure is a class of kernel-cokernel pairs stable under isomorphisms,
compositions, admissible pushouts, and admissible pullbacks. -/
@[stacks 05SF "exact structure"]
structure ExactStructure (A : Type u) [Category.{v} A] [Preadditive A]
    [HasFiniteProducts A] where
  /-- The admissible kernel-cokernel pairs. -/
  admissible : Set (ShortComplex A)
  /-- Every admissible short complex is a kernel-cokernel pair. -/
  isKernelCokernelPair {S : ShortComplex A} : admissible S → IsKernelCokernelPair S
  /-- Admissibility is invariant under isomorphism of short complexes. -/
  ofIso {S T : ShortComplex A} (e : S ≅ T) : admissible S → admissible T
  /-- Identity morphisms are admissible monomorphisms. -/
  id_admissibleMono (X : A) : IsAdmissibleMono admissible (𝟙 X)
  /-- Identity morphisms are admissible epimorphisms. -/
  id_admissibleEpi (X : A) : IsAdmissibleEpi admissible (𝟙 X)
  /-- Admissible monomorphisms are stable under composition. -/
  comp_admissibleMono {X Y Z : A} {i : X ⟶ Y} {j : Y ⟶ Z}
      (_ : IsAdmissibleMono admissible i) (_ : IsAdmissibleMono admissible j) :
      IsAdmissibleMono admissible (i ≫ j)
  /-- Admissible epimorphisms are stable under composition. -/
  comp_admissibleEpi {X Y Z : A} {p : X ⟶ Y} {q : Y ⟶ Z}
      (_ : IsAdmissibleEpi admissible p) (_ : IsAdmissibleEpi admissible q) :
      IsAdmissibleEpi admissible (p ≫ q)
  /-- Pushouts of admissible monomorphisms exist and remain admissible. -/
  pushout_admissibleMono {X Y X' : A} (i : X ⟶ Y) (f : X ⟶ X')
      (_ : IsAdmissibleMono admissible i) :
      ∃ (_ : HasPushout i f), IsAdmissibleMono admissible (pushout.inr i f)
  /-- Pullbacks of admissible epimorphisms exist and remain admissible. -/
  pullback_admissibleEpi {Y Z Z' : A} (p : Y ⟶ Z) (f : Z' ⟶ Z)
      (_ : IsAdmissibleEpi admissible p) :
      ∃ (_ : HasPullback p f), IsAdmissibleEpi admissible (pullback.snd p f)

namespace ExactStructure

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasFiniteProducts A]

/-- The admissible monomorphisms of an exact structure. -/
def AdmissibleMono (E : ExactStructure A) {X Y : A} (i : X ⟶ Y) : Prop :=
  IsAdmissibleMono E.admissible i

/-- The admissible epimorphisms of an exact structure. -/
def AdmissibleEpi (E : ExactStructure A) {Y Z : A} (p : Y ⟶ Z) : Prop :=
  IsAdmissibleEpi E.admissible p

/-- Admissibility of short complexes is invariant under isomorphism. -/
theorem admissible_iff_of_iso (E : ExactStructure A) {S T : ShortComplex A} (e : S ≅ T) :
    E.admissible S ↔ E.admissible T := sorry

/-- An admissible monomorphism is a monomorphism. -/
theorem mono_of_admissibleMono (E : ExactStructure A) {X Y : A} {i : X ⟶ Y}
    (hi : E.AdmissibleMono i) : Mono i := sorry

/-- An admissible epimorphism is an epimorphism. -/
theorem epi_of_admissibleEpi (E : ExactStructure A) {X Y : A} {p : X ⟶ Y}
    (hp : E.AdmissibleEpi p) : Epi p := sorry

/-- Every isomorphism is an admissible monomorphism for an exact structure. -/
theorem admissibleMono_of_isIso (E : ExactStructure A) {X Y : A} (i : X ⟶ Y) [IsIso i] :
    E.AdmissibleMono i := sorry

/-- Every isomorphism is an admissible epimorphism for an exact structure. -/
theorem admissibleEpi_of_isIso (E : ExactStructure A) {X Y : A} (p : X ⟶ Y) [IsIso p] :
    E.AdmissibleEpi p := sorry

end ExactStructure

end CategoryTheory
