module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.InverseSystem.HomOver
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived cross-index morphisms of ordinary left module systems

An ordinary left DG-module system has a canonical derived object at every stage.  A
cross-index morphism is a map from a later derived stage to the restriction of an earlier
derived stage along the corresponding opposite DGA transition.
-/

@[expose] public section

noncomputable section

universe u x v

open CategoryTheory Opposite

namespace DifferentialGradedModule.InverseSystem.LeftSystem.Derived

variable {R : Type u} [CommRing R]

/-- The derived stage of an ordinary left DG-module inverse system. -/
@[stacks 0GZI "derived stages of ordinary left DG-module systems"]
abbrev stage
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    (N : LeftSystem.{u, x, v} A) (n : ℕ) :=
  (DifferentialGradedModule.InverseSystem.Derived.Left.stageSource A n).obj N

/-- A derived morphism from stage `j` of `N` to the restriction of stage `i` of `N'`, for
`i ≤ j`. -/
@[stacks 0GZI "cross-index derived morphisms of ordinary left DG-module systems"]
abbrev HomOver
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    (N N' : LeftSystem.{u, x, v} A) {i j : ℕ} (hij : i ≤ j) :=
  stage A N j ⟶
    (DifferentialGradedModule.InverseSystem.Derived.Left.restriction A hij).obj
      (stage A N' i)

namespace HomOver

/-- The identity derived cross-index morphism over a reflexive inequality. -/
noncomputable def id
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    (N : LeftSystem.{u, x, v} A) (i : ℕ) :
    HomOver A N N (le_refl i) :=
  (DifferentialGradedModule.InverseSystem.Derived.Left.restrictionReflIso A i).hom.app
    (stage A N i)

/-- The canonical derived cross-index morphism induced by an ordinary left-system
transition. -/
@[stacks 0GZI "derived transition of an ordinary left DG-module system"]
noncomputable def transition
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    (N : LeftSystem.{u, x, v} A) {i j : ℕ} (hij : i ≤ j) :
    HomOver A N N hij :=
  DifferentialGradedModule.InverseSystem.Derived.Restriction.sourceApp
    (A ⋙ CochainDGAlgebra.oppositeFunctor R) hij N

/-- Composition of consecutive derived cross-index morphisms, using the canonical
composition comparison for derived restriction. -/
noncomputable def comp
    {A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)}
    {L M N : LeftSystem.{u, x, v} A} {i j k : ℕ}
    {hij : i ≤ j} {hjk : j ≤ k}
    (f : HomOver A L M hjk) (g : HomOver A M N hij) :
    HomOver A L N (Nat.le_trans hij hjk) :=
  f ≫
    (DifferentialGradedModule.InverseSystem.Derived.Left.restriction A hjk).map g ≫
    (DifferentialGradedModule.InverseSystem.Derived.Left.restrictionCompIso
      A hij hjk).hom.app (stage A N i)

/-- Composing with the identity at the target stage leaves a derived cross-index morphism
unchanged. -/
@[simp]
theorem comp_id
    {A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)}
    {L M : LeftSystem.{u, x, v} A} {i j : ℕ} {hij : i ≤ j}
    (f : HomOver A L M hij) :
    comp f (id A M i) = f := sorry

/-- Composing with the identity at the source stage leaves a derived cross-index morphism
unchanged. -/
@[simp]
theorem id_comp
    {A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)}
    {L M : LeftSystem.{u, x, v} A} {i j : ℕ} {hij : i ≤ j}
    (f : HomOver A L M hij) :
    comp (id A L j) f = f := sorry

/-- Composition of three consecutive derived cross-index morphisms is associative. -/
theorem comp_assoc
    {A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)}
    {K L M N : LeftSystem.{u, x, v} A} {i j k l : ℕ}
    {hij : i ≤ j} {hjk : j ≤ k} {hkl : k ≤ l}
    (f : HomOver A K L hkl) (g : HomOver A L M hjk)
    (h : HomOver A M N hij) :
    comp (comp f g) h = comp f (comp g h) := sorry

/-- The canonical derived transition over a reflexive inequality is the identity
cross-index morphism. -/
@[simp]
theorem transition_refl
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    (N : LeftSystem.{u, x, v} A) (i : ℕ) :
    transition A N (le_refl i) = id A N i := sorry

/-- The canonical derived transition through an intermediate stage is the composite of the
two canonical derived transitions. -/
theorem transition_comp
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    (N : LeftSystem.{u, x, v} A) {i j k : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) :
    transition A N (Nat.le_trans hij hjk) =
      comp (transition A N hjk) (transition A N hij) := sorry

/-- Send a source-shaped cross-index morphism through the global localization, using the
canonical factorization isomorphisms at its source and target stages. -/
@[stacks 0GZI "localization of cross-index morphisms of left module systems"]
noncomputable def toGlobal
    {A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)}
    {N N' : LeftSystem.{u, x, v} A} {i j : ℕ} {hij : i ≤ j}
    (f : HomOver A N N' hij) :
    DifferentialGradedModule.InverseSystem.Derived.Left.HomOver A
      ((DifferentialGradedModule.InverseSystem.Derived.Left.Q A).obj N)
      ((DifferentialGradedModule.InverseSystem.Derived.Left.Q A).obj N') hij :=
  (DifferentialGradedModule.InverseSystem.Derived.Left.evalFactors A j).hom.app N ≫
    f ≫
      (DifferentialGradedModule.InverseSystem.Derived.Left.restriction A hij).map
        ((DifferentialGradedModule.InverseSystem.Derived.Left.evalFactors A i).inv.app N')

/-- Localization carries an identity source-shaped cross-index morphism to the global
identity cross-index morphism. -/
@[simp]
theorem toGlobal_id
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    (N : LeftSystem.{u, x, v} A) (i : ℕ) :
    toGlobal (id A N i) =
      DifferentialGradedModule.InverseSystem.Derived.Left.HomOver.id A
        ((DifferentialGradedModule.InverseSystem.Derived.Left.Q A).obj N) i := sorry

/-- Localization carries the source-shaped transition to the canonical global transition. -/
@[simp]
theorem toGlobal_transition
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    (N : LeftSystem.{u, x, v} A) {i j : ℕ} (hij : i ≤ j) :
    toGlobal (transition A N hij) =
      DifferentialGradedModule.InverseSystem.Derived.Left.HomOver.transition A
        ((DifferentialGradedModule.InverseSystem.Derived.Left.Q A).obj N) hij := sorry

/-- Localization preserves composition of source-shaped cross-index morphisms. -/
theorem toGlobal_comp
    {A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)}
    {L M N : LeftSystem.{u, x, v} A} {i j k : ℕ}
    {hij : i ≤ j} {hjk : j ≤ k}
    (f : HomOver A L M hjk) (g : HomOver A M N hij) :
    toGlobal (comp f g) =
      DifferentialGradedModule.InverseSystem.Derived.Left.HomOver.comp
        (toGlobal f) (toGlobal g) := sorry

end HomOver

end DifferentialGradedModule.InverseSystem.LeftSystem.Derived
