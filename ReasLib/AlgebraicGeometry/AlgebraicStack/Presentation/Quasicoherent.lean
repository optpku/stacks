/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Presentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent.Quotient
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.LocalEquivalence.Extension

/-! # Quasi-coherent modules on a presentation of an algebraic stack -/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Presentation

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- The equivalence from a presentation quotient to the stack is a local equivalence
for the big fppf topology. -/
theorem qcohEquivalence_laws (P : Presentation X) :
    Hom.IsLocalEquivalence (Scheme.fppfTopology.over S) P.hom := sorry

/-- Pullback to a presentation quotient is an equivalence on quasi-coherent modules;
its inverse is compatible-section extension along the presentation morphism. -/
def qcohEquivalence (P : Presentation X) :
    GroupoidsOver.QCoh X ≌ GroupoidsOver.QCoh
      (GroupoidAlgebraicSpace.SmallQuotient.quotientStack P.groupoid) :=
  GroupoidsOver.LocalEquivalenceModules.qcohEquivalence P.hom (qcohEquivalence_laws P)

/-- Quasi-coherent modules on an algebraic stack are canonically equivalent to
 equivariant quasi-coherent modules on a presentation groupoid. -/
def equivariantEquivalence (P : Presentation X) :
    GroupoidsOver.QCoh X ≌ P.groupoid.QCoh :=
  (qcohEquivalence P).trans (GroupoidsOver.QCoh.toGroupoidEquivalence P.groupoid)

/-- Presentation descent first pulls back to the quotient and then restricts to
 the quotient atlas. -/
theorem equivariantEquivalence_functor (P : Presentation X) :
    (equivariantEquivalence P).functor =
      (qcohEquivalence P).functor ⋙
        (GroupoidsOver.QCoh.toGroupoidEquivalence P.groupoid).functor := rfl

/-- Reconstruction from equivariant modules first reconstructs on the quotient
 and then extends along the presentation morphism. -/
theorem equivariantEquivalence_inverse (P : Presentation X) :
    (equivariantEquivalence P).inverse =
      (GroupoidsOver.QCoh.toGroupoidEquivalence P.groupoid).inverse ⋙
        (qcohEquivalence P).inverse := rfl

end AlgebraicGeometry.AlgebraicStack.Presentation
