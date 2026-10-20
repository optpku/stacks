/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Locus
public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.FlatOverAt
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Relative.TensorPullback
public import ReasLib.AlgebraicGeometry.Scheme.WeaklyAssociatedPoints

/-!
# Flat loci over schemes with locally finite weakly associated points

For a finite-type quasicoherent module over a locally finitely presented morphism, local
finiteness of the weakly associated points of the base makes its relative flatness locus open.
On this locus, the module is finitely presented and flat over the base.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- If `f : X ⟶ S` is locally of finite presentation, `F` is a quasicoherent finite-type
module on `X`, and `S.weakAss` is locally finite, then the locus where `F` is flat over `S`
is open. -/
@[stacks 05IK]
theorem isOpen_flatOverAt_of_locallyFinite_weakAss
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h_weakAss : LocallyFinite (fun s : S.weakAss ↦ ({s.1} : Set S))) :
    IsOpen {x : X | flatOverAt F f x} := sorry

/-- The open locus on which `F` is flat over `S`, assuming local finiteness of the weakly
associated points of `S`. -/
def flatOverLocus {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h_weakAss : LocallyFinite (fun s : S.weakAss ↦ ({s.1} : Set S))) : X.Opens :=
  ⟨{x : X | flatOverAt F f x},
    isOpen_flatOverAt_of_locallyFinite_weakAss f F h_weakAss⟩

/-- Membership in `flatOverLocus f F h_weakAss` is pointwise flatness over the base. -/
@[simp]
theorem mem_flatOverLocus {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h_weakAss : LocallyFinite (fun s : S.weakAss ↦ ({s.1} : Set S))) (x : X) :
    x ∈ flatOverLocus f F h_weakAss ↔ flatOverAt F f x := sorry

/-- On the relative-flatness locus, the restriction of `F` is finitely presented. -/
@[stacks 05IK]
instance flatOverLocus_isFinitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h_weakAss : LocallyFinite (fun s : S.weakAss ↦ ({s.1} : Set S))) :
    (F.restrict (flatOverLocus f F h_weakAss).ι).IsFinitePresentation := sorry

/-- On the relative-flatness locus, the restriction of `F` is flat over `S`. -/
@[stacks 05IK]
instance flatOverLocus_isFlatOver
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h_weakAss : LocallyFinite (fun s : S.weakAss ↦ ({s.1} : Set S))) :
    flatOver (F.restrict (flatOverLocus f F h_weakAss).ι)
      ((flatOverLocus f F h_weakAss).ι ≫ f) := sorry

end AlgebraicGeometry.Scheme.Modules
