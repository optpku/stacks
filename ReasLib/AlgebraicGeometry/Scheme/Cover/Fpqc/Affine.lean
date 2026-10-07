module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc

/-!
# Singleton fpqc covering criteria

Affine spectrum families are fpqc precisely for faithfully flat ring maps.
Flat, surjective, quasi-compact scheme morphisms also give singleton covers.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Fpqc

/-- A singleton affine spectrum family is fpqc exactly when its ring map is
faithfully flat. -/
theorem covering_spec_iff_faithfullyFlat
    {A B : CommRingCat.{u}} (f : A ⟶ B) :
    Scheme.FpqcCovering
        (fun _ : PUnit ↦ CategoryTheory.Over.mk (Spec.map f)) ↔
      f.hom.FaithfullyFlat := sorry

/-- A flat, surjective, quasi-compact morphism gives a singleton fpqc covering
family. -/
theorem covering_singleton_of_flat_surjective_quasiCompact
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f] [QuasiCompact f] :
    Scheme.FpqcCovering (fun _ : Unit ↦ CategoryTheory.Over.mk f) := sorry

end AlgebraicGeometry.Scheme.Fpqc
