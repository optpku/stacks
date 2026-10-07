module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.InverseSystem.Transition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cross-index morphisms of global left derived module systems

A cross-index morphism from `N` at stage `j` to `N'` at stage `i ≤ j` is a morphism in the
derived category over the later opposite DGA, with the earlier object restricted along the DGA
transition. These morphisms compose using the canonical coherence of derived restriction.
-/

@[expose] public section

noncomputable section

universe u x v

open CategoryTheory Opposite

namespace DifferentialGradedModule.InverseSystem.Derived.Left

variable {R : Type u} [CommRing R]

/-- A morphism from a global left derived system `N` at stage `j` to a system `N'` at stage
`i ≤ j`, expressed in the derived category over `(A.obj (op j)).opposite`. -/
@[stacks 0GZI "cross-index morphisms of global left derived systems"]
abbrev HomOver
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    (N N' : Category.{u, x, v} A) {i j : ℕ} (hij : i ≤ j) :=
  (eval A j).obj N ⟶ (restriction A hij).obj ((eval A i).obj N')

namespace HomOver

/-- The identity cross-index morphism over a reflexive inequality. -/
noncomputable def id
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    (N : Category.{u, x, v} A) (i : ℕ) :
    HomOver A N N (le_refl i) :=
  (restrictionReflIso A i).hom.app ((eval A i).obj N)

/-- The canonical cross-index morphism supplied by the transition of a global left derived
system. -/
@[stacks 0GZI "canonical cross-index transition of a global left derived system"]
noncomputable def transition
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    (N : Category.{u, x, v} A) {i j : ℕ} (hij : i ≤ j) :
    HomOver A N N hij :=
  (comparison A hij).app N

/-- Compose consecutive cross-index morphisms, restricting the second morphism to the later
derived category before applying restriction-composition coherence. -/
noncomputable def comp
    {A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)}
    {L M N : Category.{u, x, v} A} {i j k : ℕ}
    {hij : i ≤ j} {hjk : j ≤ k}
    (f : HomOver A L M hjk) (g : HomOver A M N hij) :
    HomOver A L N (Nat.le_trans hij hjk) :=
  f ≫ (restriction A hjk).map g ≫
    (restrictionCompIso A hij hjk).hom.app ((eval A i).obj N)

/-- Composition with an identity cross-index morphism at the target stage does not change a
cross-index morphism. -/
@[simp]
theorem comp_id
    {A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)}
    {L M : Category.{u, x, v} A} {i j : ℕ} {hij : i ≤ j}
    (f : HomOver A L M hij) :
    comp f (id A M i) = f := sorry

/-- Composition with an identity cross-index morphism at the source stage does not change a
cross-index morphism. -/
@[simp]
theorem id_comp
    {A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)}
    {L M : Category.{u, x, v} A} {i j : ℕ} {hij : i ≤ j}
    (f : HomOver A L M hij) :
    comp (id A L j) f = f := sorry

/-- Composition of three consecutive cross-index morphisms is associative. -/
theorem comp_assoc
    {A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)}
    {K L M N : Category.{u, x, v} A} {i j k l : ℕ}
    {hij : i ≤ j} {hjk : j ≤ k} {hkl : k ≤ l}
    (f : HomOver A K L hkl) (g : HomOver A L M hjk)
    (h : HomOver A M N hij) :
    comp (comp f g) h = comp f (comp g h) := sorry

/-- The canonical transition over a reflexive inequality is the identity cross-index
morphism. -/
@[simp]
theorem transition_refl
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    (N : Category.{u, x, v} A) (i : ℕ) :
    transition A N (le_refl i) = id A N i := sorry

/-- A canonical transition through an intermediate index is the composite of the two canonical
cross-index transitions. -/
theorem transition_comp
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    (N : Category.{u, x, v} A) {i j k : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) :
    transition A N (Nat.le_trans hij hjk) =
      comp (transition A N hjk) (transition A N hij) := sorry

end HomOver

end DifferentialGradedModule.InverseSystem.Derived.Left
