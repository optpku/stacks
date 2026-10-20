module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalHomotopy
public import Mathlib.Order.Defs.Unbundled

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- Formal homotopy is an equivalence relation on morphisms between any two
complete local algebras. -/
@[stacks 0DQB]
theorem FormallyHomotopic.equivalence {R S : CompleteLocalAlgCat Λ k} :
    _root_.Equivalence (FormallyHomotopic : (R ⟶ S) → (R ⟶ S) → Prop) := sorry

/-- Every morphism of complete local algebras is formally homotopic to itself. -/
@[refl]
theorem FormallyHomotopic.refl {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S) :
    FormallyHomotopic f f :=
  (FormallyHomotopic.equivalence (R := R) (S := S)).refl f

/-- If one morphism of complete local algebras is formally homotopic to another,
the second is formally homotopic to the first. -/
@[symm]
theorem FormallyHomotopic.symm {R S : CompleteLocalAlgCat Λ k} {f g : R ⟶ S} :
    FormallyHomotopic f g → FormallyHomotopic g f :=
  (FormallyHomotopic.equivalence (R := R) (S := S)).symm

/-- Formal homotopies between successive morphisms of complete local algebras
imply a formal homotopy between the first and the last. -/
@[trans]
theorem FormallyHomotopic.trans {R S : CompleteLocalAlgCat Λ k} {f g h : R ⟶ S} :
    FormallyHomotopic f g → FormallyHomotopic g h → FormallyHomotopic f h :=
  (FormallyHomotopic.equivalence (R := R) (S := S)).trans

/-- Formal homotopy has the canonical equivalence-relation property on each
set of morphisms between complete local algebras. -/
instance FormallyHomotopic.instIsEquiv {R S : CompleteLocalAlgCat Λ k} :
    IsEquiv (R ⟶ S) FormallyHomotopic :=
  IsEquiv.of_equivalence FormallyHomotopic.equivalence

end CompleteLocalAlgCat
