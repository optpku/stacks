/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Adjunction.ProjectionFormula
public import ReasLib.CategoryTheory.Monoidal.Duality.Adjunction
public import ReasLib.CategoryTheory.Monoidal.Duality.Dualizable
public import ReasLib.CategoryTheory.Monoidal.Duality.Functor
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection formulas for dualizable objects

A strong monoidal left adjoint satisfies the projection formula on every right-dualizable
object.  The exact-pairing statement is the data-level interface; the object-property statement
is the choice-free interface intended for geometric finiteness hypotheses.
-/

@[expose] public section

open CategoryTheory.MonoidalCategory

noncomputable section

universe u₁ v₁ u₂ v₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
variable {L : C ⥤ D} {R : D ⥤ C} [L.Monoidal]

namespace ExactPairing

/-- The explicit projection-formula natural isomorphism associated to chosen right-duality data.
It is obtained by identifying the two left adjoints and conjugating that identification to their
right adjoints. -/
@[stacks 0E8I "exact-pairing natural isomorphism"]
noncomputable def projectionFormulaNatIso
    {X X' : C} (p : ExactPairing X X') (adj : L ⊣ R) :
    R ⋙ tensorLeft X ≅ tensorLeft (L.obj X) ⋙ R :=
  conjugateIsoEquiv
    (p.tensorLeftAdjunction.comp adj)
    (adj.comp ((p.map L).tensorLeftAdjunction))
    (Functor.Monoidal.commTensorLeft L X')

/-- The forward map of the exact-pairing projection-formula isomorphism is the canonical mate. -/
@[simp]
theorem projectionFormulaNatIso_hom
    {X X' : C} (p : ExactPairing X X') (adj : L ⊣ R) :
    (p.projectionFormulaNatIso adj).hom =
      adj.projectionFormulaMateNatTrans X := sorry

/-- The explicit left projection-formula natural isomorphism associated to chosen left-duality
data. -/
@[stacks 0E8I "left exact-pairing natural isomorphism"]
noncomputable def leftProjectionFormulaNatIso
    {X X' : C} (p : ExactPairing X' X) (adj : L ⊣ R) :
    R ⋙ tensorRight X ≅ tensorRight (L.obj X) ⋙ R :=
  conjugateIsoEquiv
    (p.tensorRightAdjunction.comp adj)
    (adj.comp ((p.map L).tensorRightAdjunction))
    (Functor.Monoidal.commTensorRight L X')

/-- The forward map of the exact-pairing left projection-formula isomorphism is the canonical
left mate. -/
@[simp]
theorem leftProjectionFormulaNatIso_hom
    {X X' : C} (p : ExactPairing X' X) (adj : L ⊣ R) :
    (p.leftProjectionFormulaNatIso adj).hom =
      adj.leftProjectionFormulaMateNatTrans X := sorry

/-- For a strong monoidal left adjoint, the projection-formula mate at an object equipped with
an explicit right dual is an isomorphism. -/
@[stacks 0E8I "exact-pairing form"]
theorem isIso_projectionFormulaMate
    {X X' : C} (p : ExactPairing X X') (adj : L ⊣ R) (Y : D) :
    IsIso (adj.projectionFormulaMate X Y) := sorry

/-- For a strong monoidal left adjoint, the left projection-formula mate at an object equipped
with an explicit left dual is an isomorphism. -/
@[stacks 0E8I "left exact-pairing form"]
theorem isIso_leftProjectionFormulaMate
    {X X' : C} (p : ExactPairing X' X) (adj : L ⊣ R) (Y : D) :
    IsIso (adj.leftProjectionFormulaMate Y X) := sorry

end ExactPairing

namespace IsRightDualizable

/-- A strong monoidal left adjoint satisfies the projection formula at every right-dualizable
object. -/
@[stacks 0E8I "right-dualizable form"]
theorem isIso_projectionFormulaMate
    {X : C} (hX : IsRightDualizable X) (adj : L ⊣ R) (Y : D) :
    IsIso (adj.projectionFormulaMate X Y) := sorry

/-- For a fixed right-dualizable object, the projection-formula mates form an invertible natural
transformation. -/
theorem isIso_projectionFormulaMateNatTrans
    {X : C} (hX : IsRightDualizable X) (adj : L ⊣ R) :
    IsIso (adj.projectionFormulaMateNatTrans X) := sorry

/-- The functorial projection-formula isomorphism associated to a right-dualizable source-side
factor. -/
@[stacks 0E8I "right-dualizable natural isomorphism"]
noncomputable def projectionFormulaNatIso
    {X : C} (hX : IsRightDualizable X) (adj : L ⊣ R) :
    R ⋙ tensorLeft X ≅ tensorLeft (L.obj X) ⋙ R :=
  (Classical.choice hX).exact.projectionFormulaNatIso adj

/-- The chosen-dual construction has the canonical projection-formula mate as its forward map. -/
@[simp]
theorem projectionFormulaNatIso_hom
    {X : C} (hX : IsRightDualizable X) (adj : L ⊣ R) :
    (hX.projectionFormulaNatIso adj).hom =
      adj.projectionFormulaMateNatTrans X := sorry

end IsRightDualizable

namespace IsLeftDualizable

/-- A strong monoidal left adjoint satisfies the left projection formula at every left-dualizable
object. -/
@[stacks 0E8I "left-dualizable form"]
theorem isIso_leftProjectionFormulaMate
    {X : C} (hX : IsLeftDualizable X) (adj : L ⊣ R) (Y : D) :
    IsIso (adj.leftProjectionFormulaMate Y X) := sorry

/-- For a fixed left-dualizable object, the left projection-formula mates form an invertible
natural transformation. -/
theorem isIso_leftProjectionFormulaMateNatTrans
    {X : C} (hX : IsLeftDualizable X) (adj : L ⊣ R) :
    IsIso (adj.leftProjectionFormulaMateNatTrans X) := sorry

/-- The functorial left projection-formula isomorphism associated to a left-dualizable
source-side factor. -/
@[stacks 0E8I "left-dualizable natural isomorphism"]
noncomputable def leftProjectionFormulaNatIso
    {X : C} (hX : IsLeftDualizable X) (adj : L ⊣ R) :
    R ⋙ tensorRight X ≅ tensorRight (L.obj X) ⋙ R :=
  (Classical.choice hX).exact.leftProjectionFormulaNatIso adj

/-- The chosen-left-dual construction has the canonical left projection-formula mate as its
forward map. -/
@[simp]
theorem leftProjectionFormulaNatIso_hom
    {X : C} (hX : IsLeftDualizable X) (adj : L ⊣ R) :
    (hX.leftProjectionFormulaNatIso adj).hom =
      adj.leftProjectionFormulaMateNatTrans X := sorry

end IsLeftDualizable

end CategoryTheory
