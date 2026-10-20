/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint
public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf
public import ReasLib.RingTheory.Henselian.StrictHenselization
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.IsSepClosed

open CategoryTheory Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale.Small

universe u v

@[expose] public section

noncomputable section

namespace AlgebraicGeometry.Scheme

/-- A strict henselization of the local ring at a geometric point is identified with the stalk of
the étale structure sheaf at that point. -/
theorem strictHenselization_iso_etaleStructureSheafStalk
    (S : Scheme.{u}) (s : GeometricPoint S)
    (Rsh : Type v) [CommRing Rsh]
    [Algebra (S.presheaf.stalk s.image) Rsh]
    [IsStrictHenselizationOf (S.presheaf.stalk s.image) Rsh] :
    Nonempty (Rsh ≃+*
      ((@Scheme.pointSmallEtale S s.K inferInstance
        (@IsSepClosed.of_isAlgClosed s.K inferInstance s.isAlgClosed) s.hom).presheafFiber :
        (S.Etaleᵒᵖ ⥤ RingCat) ⥤ RingCat).obj
        (structureSheaf S).obj) := sorry

end AlgebraicGeometry.Scheme
