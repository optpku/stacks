module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo.ModuleCech
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections

/-!
# Glueable global sections over Spec R

A scheme over `Spec R` has glueable global sections for `(R → R', f)` when the
Beauville-Laszlo module Cech sequence of `Γ(T.left, ⊤)` is short exact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The structure morphism of a scheme over `Spec R` induces the `R`-algebra
structure on global sections. -/
instance instAlgebra_overSpec {R : Type u} [CommRing R]
    (T : Over (Spec (CommRingCat.of R))) :
    Algebra R Γ(T.left, ⊤) :=
  globalSectionsAlgebra T.hom

/-- Global sections of a scheme `T` over `Spec R` are glueable as an `R`-module
when the Beauville-Laszlo module Cech sequence of `Γ(T.left, ⊤)` is short exact. -/
abbrev glueableGlobalSections {R : Type u} [CommRing R]
    (R' : Type u) [CommRing R'] [Algebra R R'] (f : R)
    (T : Over (Spec (CommRingCat.of R))) : Prop :=
  (beauvilleLaszloModuleCechSequence R' Γ(T.left, ⊤) f).ShortExact

/-- Glueability of global sections is short exactness of the module Cech sequence. -/
theorem glueableGlobalSections_iff {R : Type u} [CommRing R]
    (R' : Type u) [CommRing R'] [Algebra R R'] (f : R)
    (T : Over (Spec (CommRingCat.of R))) :
    glueableGlobalSections R' f T ↔
      (beauvilleLaszloModuleCechSequence R' Γ(T.left, ⊤) f).ShortExact :=
  sorry

end AlgebraicGeometry.Scheme.Hom
