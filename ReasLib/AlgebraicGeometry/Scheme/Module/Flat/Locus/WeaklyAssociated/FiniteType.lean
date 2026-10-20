/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Locus.WeaklyAssociated
public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.Relative

/-!
# Flat loci for finite-type modules over locally finite-type morphisms

For a finite-type quasicoherent module over a locally finite-type morphism, local finiteness
of the weakly associated points of the base makes its relative flatness locus open. On this
locus, the module is flat and finitely presented relative to the base.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

namespace IsFiniteType

/-- If `f : X ⟶ S` is locally of finite type, `F` is a quasicoherent finite-type module on
`X`, and `S.weakAss` is locally finite, then the locus where `F` is flat over `S` is open. -/
theorem isOpen_flatOverAt_of_locallyFinite_weakAss
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h_weakAss : LocallyFinite (fun s : S.weakAss ↦ ({s.1} : Set S))) :
    IsOpen {x : X | flatOverAt F f x} := sorry

/-- The open locus on which a finite-type module `F` is flat over `S`. -/
def flatOverLocus {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h_weakAss : LocallyFinite (fun s : S.weakAss ↦ ({s.1} : Set S))) : X.Opens :=
  ⟨{x : X | flatOverAt F f x},
    isOpen_flatOverAt_of_locallyFinite_weakAss f F h_weakAss⟩

/-- Membership in `flatOverLocus f F h_weakAss` is pointwise flatness over the base. -/
@[simp]
theorem mem_flatOverLocus {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h_weakAss : LocallyFinite (fun s : S.weakAss ↦ ({s.1} : Set S))) (x : X) :
    x ∈ flatOverLocus f F h_weakAss ↔ flatOverAt F f x := sorry

/-- On the relative-flatness locus, the restriction of `F` is flat over `S`. -/
instance flatOverLocus_isFlatOver
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h_weakAss : LocallyFinite (fun s : S.weakAss ↦ ({s.1} : Set S))) :
    flatOver (F.restrict (flatOverLocus f F h_weakAss).ι)
      ((flatOverLocus f F h_weakAss).ι ≫ f) := sorry

/-- On the relative-flatness locus, the restriction of `F` is finitely presented relative to
`S`. -/
theorem flatOverLocus_isFinitePresentationOver
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h_weakAss : LocallyFinite (fun s : S.weakAss ↦ ({s.1} : Set S))) :
    (F.restrict (flatOverLocus f F h_weakAss).ι).IsFinitePresentationOver
      ((flatOverLocus f F h_weakAss).ι ≫ f) := sorry

end IsFiniteType

/-- For a locally finitely presented morphism, the finite-type flat locus agrees with the
flat locus constructed under the stronger morphism hypothesis. -/
theorem IsFiniteType.flatOverLocus_eq_flatOverLocus
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h_weakAss : LocallyFinite (fun s : S.weakAss ↦ ({s.1} : Set S))) :
    IsFiniteType.flatOverLocus f F h_weakAss = flatOverLocus f F h_weakAss := sorry

end AlgebraicGeometry.Scheme.Modules
