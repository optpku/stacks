/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.EtaleLocal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SourceLocus.Etale

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Germ.MorphismProperty

/-- The property of a germ morphism that some representative has the scheme-morphism
property `P`. -/
def representedBy (P : CategoryTheory.MorphismProperty Scheme.{u}) :
    CategoryTheory.MorphismProperty Germ :=
  fun {X Y} f ↦ ∃ r : Hom.Representative X Y, Hom.mk r = f ∧ P r.hom

/-- A germ morphism is `representedBy P` exactly when it has a representative satisfying `P`. -/
theorem representedBy_iff (P : CategoryTheory.MorphismProperty Scheme.{u})
    {X Y : Germ} (f : X ⟶ Y) :
    representedBy P f ↔ ∃ r : Hom.Representative X Y, Hom.mk r = f ∧ P r.hom := sorry

/-- A representative satisfying `P` gives a germ morphism with property `representedBy P`. -/
theorem representedBy_ofRepresentative (P : CategoryTheory.MorphismProperty Scheme.{u})
    {X Y : Germ} (r : Hom.Representative X Y) (hr : P r.hom) :
    representedBy P (Hom.mk r) := sorry

/-- For a property étale local on the source, `representedBy P` for a given representative
is membership of its distinguished point in the source locus of `P`. -/
theorem representedBy_mk_iff (P : CategoryTheory.MorphismProperty Scheme.{u})
    [P.IsLocalAtSource Scheme.etalePrecoverage] {X Y : Germ}
    (r : Hom.Representative X Y) :
    representedBy P (Hom.mk r) ↔
      X.pointIn r.neighborhood r.mem_neighborhood ∈ P.sourceLocus r.hom := sorry

/-- If a scheme-morphism property is étale local on source-and-target, then the property
that a germ morphism has a representative satisfying it is likewise étale local. -/
theorem representedBy_isEtaleLocal
    (P : CategoryTheory.MorphismProperty Scheme.{u})
    [IsEtaleLocalAtSourceAndTarget P] : IsEtaleLocal (representedBy P) := sorry

end AlgebraicGeometry.Scheme.Germ.MorphismProperty

namespace AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget

open Scheme.Germ

/-- A scheme morphism has an étale-local-on-source-and-target property exactly when
every induced morphism of germs has the associated represented property. -/
theorem iff_forall_germ (P : MorphismProperty Scheme.{u})
    [IsEtaleLocalAtSourceAndTarget P] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    P f ↔ ∀ x : X, MorphismProperty.representedBy P
      (Hom.ofGlobal f rfl : Scheme.Germ.of X x ⟶ Scheme.Germ.of Y (f x)) := sorry

end AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget
