/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.AdjoinVariable.Family
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.AdjoinVariable.Predifferential.Even
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.AdjoinVariable.Predifferential.Odd

/-!
# Canonical cells as singleton adjoining families

This integration leaf equips the explicit odd and even one-cell models with their canonical
graded presentations.  It then exposes each cell as a `Unit`-indexed `Family`, without making the
generic family layer depend on either parity-specific coefficient model.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace DividedPowerChainAlgebra.Adjoin.Odd

variable {R : Type u} [CommRing R]

/-- The base inclusion into the explicit odd-variable divided-power graded algebra, with its
source and target bundles fixed for categorical composition. -/
def gradedInclusion
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ)) :
    A.toGradedAlgebra ⟶ gradedAlgebra A d hd :=
  NonnegGradedAlgebra.Adjoin.Odd.inclusionDP
    A.toChainDGAlgebra.nonnegativePart d A.gamma hd

/-- The graded lift from the explicit odd-variable algebra determined by a base map and a
singleton generator assignment. -/
def presentationLift
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    {C : DividedPowerGradedAlgebra.{u, v} R} (g : A.toGradedAlgebra ⟶ C)
    (x : Unit → C.toGradedAlgebra.piece (d : ℕ)) : gradedAlgebra A d hd ⟶ C :=
  NonnegGradedAlgebra.Adjoin.Odd.liftDP A.toChainDGAlgebra.nonnegativePart d
    A.gamma hd C.gamma g (x ())

/-- The explicit odd graded lift restricts to the prescribed base map. -/
theorem presentationLift_inclusion
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    {C : DividedPowerGradedAlgebra.{u, v} R} (g : A.toGradedAlgebra ⟶ C)
    (x : Unit → C.toGradedAlgebra.piece (d : ℕ)) :
    gradedInclusion A d hd ≫ presentationLift A d hd g x = g := sorry

/-- The explicit odd graded lift sends the generator to the singleton assignment. -/
theorem presentationLift_generator
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    {C : DividedPowerGradedAlgebra.{u, v} R} (g : A.toGradedAlgebra ⟶ C)
    (x : Unit → C.toGradedAlgebra.piece (d : ℕ)) (j : Unit) :
    (presentationLift A d hd g x).toGradedHom.map d
        (NonnegGradedAlgebra.Adjoin.Odd.generator
          A.toChainDGAlgebra.nonnegativePart d) = x j := sorry

/-- Graded maps out of the explicit odd-variable algebra are determined by the base and
singleton generator. -/
theorem gradedHom_ext
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    {C : DividedPowerGradedAlgebra.{u, v} R} (g h : gradedAlgebra A d hd ⟶ C)
    (hbase : gradedInclusion A d hd ≫ g = gradedInclusion A d hd ≫ h)
    (hgenerator : ∀ _ : Unit,
      g.toGradedHom.map d (NonnegGradedAlgebra.Adjoin.Odd.generator
        A.toChainDGAlgebra.nonnegativePart d) =
      h.toGradedHom.map d (NonnegGradedAlgebra.Adjoin.Odd.generator
        A.toChainDGAlgebra.nonnegativePart d)) :
    g = h := sorry

/-- The explicit odd-variable graded algebra with its singleton relative presentation. -/
@[stacks 09PM "graded presentation of the odd-variable algebra"]
def gradedPresentation
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ)) :
    DividedPowerGradedAlgebra.Adjoin.Presentation A.toGradedAlgebra
      (gradedAlgebra A d hd) d Unit
      (gradedInclusion A d hd)
      (fun _ ↦ NonnegGradedAlgebra.Adjoin.Odd.generator
        A.toChainDGAlgebra.nonnegativePart d) where
  lift := presentationLift A d hd
  lift_inclusion := presentationLift_inclusion A d hd
  lift_generator := presentationLift_generator A d hd
  hom_ext := gradedHom_ext A d hd

/-- The graded algebra underlying the canonical odd cell is canonically identified with the
explicit odd-variable graded algebra. -/
@[stacks 09PM "odd cell graded comparison"]
def cellGradedIso
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    (cell A d hd f hf).algebra.toGradedAlgebra ≅ gradedAlgebra A d hd :=
  eqToIso (chainAlgebra_toGradedAlgebra A d hd f hf)

/-- The inverse graded identification carries the explicit base inclusion to the cell
inclusion. -/
theorem gradedInclusion_comp_cellGradedIso_inv
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    gradedInclusion A d hd ≫ (cellGradedIso A d hd f hf).inv =
      (cell A d hd f hf).ι.toGradedHom := sorry

/-- The inverse graded identification carries the explicit odd generator to the cell
generator. -/
@[stacks 09PM "odd cell generator comparison"]
theorem cellGradedIso_inv_generator
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f)
    (j : Unit) :
    (cellGradedIso A d hd f hf).inv.toGradedHom.map d
        (NonnegGradedAlgebra.Adjoin.Odd.generator
          A.toChainDGAlgebra.nonnegativePart d) = (cell A d hd f hf).generator := sorry

/-- The canonical odd cell carries the graded presentation transported from its explicit
exterior-variable model. -/
@[stacks 09PM "graded presentation of the canonical odd cell"]
def cellGradedPresentation
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    (cell A d hd f hf).GradedPresentation :=
    (gradedPresentation A d hd).ofIso (cellGradedIso A d hd f hf).symm
    (cell A d hd f hf).ι.toGradedHom (fun _ ↦ (cell A d hd f hf).generator)
    (gradedInclusion_comp_cellGradedIso_inv A d hd f hf)
    (cellGradedIso_inv_generator A d hd f hf)

/-- The canonical odd adjoining-variable cell as a singleton indexed family. -/
@[stacks 09PM "canonical odd cell as a singleton family"]
def family
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    Family A d (fun _ : Unit ↦ f) :=
  (cell A d hd f hf).toFamily (cellGradedPresentation A d hd f hf)

/-- The algebra of the canonical odd singleton family is the algebra of the canonical odd cell. -/
@[simp]
theorem family_algebra
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    (family A d hd f hf).algebra = (cell A d hd f hf).algebra := sorry

/-- The inclusion of the canonical odd singleton family is the inclusion of its canonical cell. -/
@[simp]
theorem family_inclusion
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    (family A d hd f hf).inclusion = (cell A d hd f hf).ι := sorry

/-- Every generator of the canonical odd singleton family is the generator of its canonical
cell. -/
@[simp]
theorem family_generator
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f)
    (j : Unit) :
    (family A d hd f hf).generator j = (cell A d hd f hf).generator := sorry

/-- The stored graded presentation of the canonical odd singleton family is the canonical
transported cell presentation. -/
@[simp]
theorem family_gradedPresentation
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    (family A d hd f hf).gradedPresentation = cellGradedPresentation A d hd f hf := sorry

/-- Forgetting the singleton-family view of the canonical odd cell recovers that cell. -/
@[simp]
theorem family_toCell
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    (family A d hd f hf).toCell = cell A d hd f hf := sorry

end DividedPowerChainAlgebra.Adjoin.Odd

namespace DividedPowerChainAlgebra.Adjoin.Even

variable {R : Type u} [CommRing R]

/-- The base inclusion into the explicit even-variable divided-power graded algebra, with its
source and target bundles fixed for categorical composition. -/
def gradedInclusion
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Even (d : ℕ)) :
    A.toGradedAlgebra ⟶ gradedAlgebra A d hd :=
  NonnegGradedAlgebra.Adjoin.Even.inclusionDP
    A.toChainDGAlgebra.nonnegativePart d A.gamma hd d.2

/-- The graded lift from the explicit even-variable algebra determined by a base map and a
singleton generator assignment. -/
def presentationLift
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Even (d : ℕ))
    {C : DividedPowerGradedAlgebra.{u, v} R} (g : A.toGradedAlgebra ⟶ C)
    (x : Unit → C.toGradedAlgebra.piece (d : ℕ)) : gradedAlgebra A d hd ⟶ C :=
  NonnegGradedAlgebra.Adjoin.Even.liftPositiveDP A.toChainDGAlgebra.nonnegativePart
    A.gamma d hd C.gamma g (x ())

/-- The explicit even graded lift restricts to the prescribed base map. -/
theorem presentationLift_inclusion
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Even (d : ℕ))
    {C : DividedPowerGradedAlgebra.{u, v} R} (g : A.toGradedAlgebra ⟶ C)
    (x : Unit → C.toGradedAlgebra.piece (d : ℕ)) :
    gradedInclusion A d hd ≫ presentationLift A d hd g x = g := sorry

/-- The explicit even graded lift sends the generator to the singleton assignment. -/
theorem presentationLift_generator
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Even (d : ℕ))
    {C : DividedPowerGradedAlgebra.{u, v} R} (g : A.toGradedAlgebra ⟶ C)
    (x : Unit → C.toGradedAlgebra.piece (d : ℕ)) (j : Unit) :
    (presentationLift A d hd g x).toGradedHom.map d
        (NonnegGradedAlgebra.Adjoin.Even.generator
          A.toChainDGAlgebra.nonnegativePart d) = x j := sorry

/-- Graded maps out of the explicit even-variable algebra are determined by the base and
singleton generator. -/
theorem gradedHom_ext
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Even (d : ℕ))
    {C : DividedPowerGradedAlgebra.{u, v} R} (g h : gradedAlgebra A d hd ⟶ C)
    (hbase : gradedInclusion A d hd ≫ g = gradedInclusion A d hd ≫ h)
    (hgenerator : ∀ _ : Unit,
      g.toGradedHom.map d (NonnegGradedAlgebra.Adjoin.Even.generator
        A.toChainDGAlgebra.nonnegativePart d) =
      h.toGradedHom.map d (NonnegGradedAlgebra.Adjoin.Even.generator
        A.toChainDGAlgebra.nonnegativePart d)) :
    g = h := sorry

/-- The explicit even-variable graded algebra with its singleton relative presentation. -/
@[stacks 09PM "graded presentation of the even-variable algebra"]
def gradedPresentation
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Even (d : ℕ)) :
    DividedPowerGradedAlgebra.Adjoin.Presentation A.toGradedAlgebra
      (gradedAlgebra A d hd) d Unit
      (gradedInclusion A d hd)
      (fun _ ↦ NonnegGradedAlgebra.Adjoin.Even.generator
        A.toChainDGAlgebra.nonnegativePart d) where
  lift := presentationLift A d hd
  lift_inclusion := presentationLift_inclusion A d hd
  lift_generator := presentationLift_generator A d hd
  hom_ext := gradedHom_ext A d hd

/-- The graded algebra underlying the canonical even cell is canonically identified with the
explicit even-variable graded algebra. -/
@[stacks 09PM "even cell graded comparison"]
def cellGradedIso
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Even (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    (cell A d hd f hf).algebra.toGradedAlgebra ≅ gradedAlgebra A d hd :=
  eqToIso (chainAlgebra_toGradedAlgebra A d hd f hf)

/-- The inverse graded identification carries the explicit base inclusion to the cell
inclusion. -/
theorem gradedInclusion_comp_cellGradedIso_inv
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Even (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    gradedInclusion A d hd ≫ (cellGradedIso A d hd f hf).inv =
      (cell A d hd f hf).ι.toGradedHom := sorry

/-- The inverse graded identification carries the explicit even generator to the cell
generator. -/
@[stacks 09PM "even cell generator comparison"]
theorem cellGradedIso_inv_generator
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Even (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f)
    (j : Unit) :
    (cellGradedIso A d hd f hf).inv.toGradedHom.map d
        (NonnegGradedAlgebra.Adjoin.Even.generator
          A.toChainDGAlgebra.nonnegativePart d) = (cell A d hd f hf).generator := sorry

/-- The canonical even cell carries the graded presentation transported from its explicit
divided-monomial model. -/
@[stacks 09PM "graded presentation of the canonical even cell"]
def cellGradedPresentation
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Even (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    (cell A d hd f hf).GradedPresentation :=
    (gradedPresentation A d hd).ofIso (cellGradedIso A d hd f hf).symm
    (cell A d hd f hf).ι.toGradedHom (fun _ ↦ (cell A d hd f hf).generator)
    (gradedInclusion_comp_cellGradedIso_inv A d hd f hf)
    (cellGradedIso_inv_generator A d hd f hf)

/-- The canonical even adjoining-variable cell as a singleton indexed family. -/
@[stacks 09PM "canonical even cell as a singleton family"]
def family
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Even (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    Family A d (fun _ : Unit ↦ f) :=
  (cell A d hd f hf).toFamily (cellGradedPresentation A d hd f hf)

/-- The algebra of the canonical even singleton family is the algebra of the canonical even cell. -/
@[simp]
theorem family_algebra
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Even (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    (family A d hd f hf).algebra = (cell A d hd f hf).algebra := sorry

/-- The inclusion of the canonical even singleton family is the inclusion of its canonical cell. -/
@[simp]
theorem family_inclusion
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Even (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    (family A d hd f hf).inclusion = (cell A d hd f hf).ι := sorry

/-- Every generator of the canonical even singleton family is the generator of its canonical
cell. -/
@[simp]
theorem family_generator
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Even (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f)
    (j : Unit) :
    (family A d hd f hf).generator j = (cell A d hd f hf).generator := sorry

/-- The stored graded presentation of the canonical even singleton family is the canonical
transported cell presentation. -/
@[simp]
theorem family_gradedPresentation
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Even (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    (family A d hd f hf).gradedPresentation = cellGradedPresentation A d hd f hf := sorry

/-- Forgetting the singleton-family view of the canonical even cell recovers that cell. -/
@[simp]
theorem family_toCell
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Even (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    (family A d hd f hf).toCell = cell A d hd f hf := sorry

end DividedPowerChainAlgebra.Adjoin.Even
