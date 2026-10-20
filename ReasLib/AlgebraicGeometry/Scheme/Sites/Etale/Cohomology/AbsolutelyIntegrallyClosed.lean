/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.RingTheory.AbsolutelyIntegrallyClosed

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- Positive-degree small-étale cohomology of the constant sheaf associated to a
finite abelian group on the spectrum of an absolutely integrally closed ring is zero. -/
theorem etaleCohomology_constant_isZero_of_isAbsolutelyIntegrallyClosed
    {R M : Type u} [CommRing R] [IsAbsolutelyIntegrallyClosed R]
    [AddCommGroup M] [Finite M]
    [HasSheafify (Spec (.of R)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    {i : ℕ} (hi : 0 < i) :
    IsZero
      ((Sheaf.functorH (Spec (.of R)).smallEtaleTopology i).obj
        ((constantSheaf (Spec (.of R)).smallEtaleTopology AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} M)))) := sorry

end AlgebraicGeometry.Scheme
