/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Scheme.FourierMukai.ConstantFamily
public import ReasLib.AlgebraicGeometry.Scheme.FourierMukai.RelativeEquivalence

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

/-- A smooth proper family over a finite-type `k`-scheme is isomorphic to its constant
fibre family near a `k`-rational point if a relative-equivalence kernel restricts to
the diagonal kernel on the fibre square. The isomorphism commutes with the structure
morphisms over the open neighbourhood. -/
@[stacks 0G0R]
theorem exists_isIso_restriction_of_relativeEquivalenceKernel_fiber_diagonal
    {k : Type u} [Field k] {S : Scheme.{u}} (hS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType hS] [QuasiCompact hS]
    (σ : Spec (.of k) ⟶ S) (hσ : σ ≫ hS = 𝟙 _)
    (s : S) (hs : s = σ (closedPoint k))
    (Y : FourierMukaiObject S)
    (K : @RingedSpace.ModuleDerived.Perfect
      (pullback (FourierMukaiObject.constantFamily hS σ hσ Y).hom Y.hom).toRingedSpace)
    [IsIso (C := FourierMukaiObject S)
      (Quotient.mk'' K : FourierMukaiObject.constantFamily hS σ hσ Y ⟶ Y)]
    (hK : IsIsomorphic
      (FourierMukaiObject.fiberSquarePullbackKernel hS σ hσ Y K)
      (FourierMukaiObject.diagonalKernel (FourierMukaiObject.fiberOver hS σ hσ Y))) :
    ∃ U : S.Opens, s ∈ U ∧ ∃
      e : (FourierMukaiObject.baseChange U.ι Y).scheme ⟶
        (FourierMukaiObject.baseChange U.ι
          (FourierMukaiObject.constantFamily hS σ hσ Y)).scheme,
      e ≫ (FourierMukaiObject.baseChange U.ι
            (FourierMukaiObject.constantFamily hS σ hσ Y)).hom =
          (FourierMukaiObject.baseChange U.ι Y).hom ∧
        IsIso e := sorry

/-- A smooth proper family over a finite-type scheme over an algebraically closed field
is locally isomorphic over the base to a constant smooth proper family if it admits
a relative-equivalence kernel from a constant smooth proper family. -/
@[stacks 0G0S]
theorem FourierMukaiObject.exists_openCover_locallyProductOfSmoothProper
    {k : Type u} [Field k] [IsAlgClosed k] {S : Scheme.{u}}
    (hS : S ⟶ Spec (.of k)) [LocallyOfFiniteType hS] [QuasiCompact hS]
    (X : FourierMukaiObject (Spec (.of k))) (Y : FourierMukaiObject S)
    (K : @RingedSpace.ModuleDerived.Perfect
      (pullback (FourierMukaiObject.baseChange hS X).hom Y.hom).toRingedSpace)
    [IsIso (C := FourierMukaiObject S)
      (Quotient.mk'' K : FourierMukaiObject.baseChange hS X ⟶ Y)] :
    ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      ∃ Y0 : FourierMukaiObject (Spec (.of k)),
        ∃ e : (FourierMukaiObject.baseChange U.ι Y).scheme ⟶
            (FourierMukaiObject.baseChange U.ι
              (FourierMukaiObject.baseChange hS Y0)).scheme,
          e ≫ (FourierMukaiObject.baseChange U.ι
                (FourierMukaiObject.baseChange hS Y0)).hom =
              (FourierMukaiObject.baseChange U.ι Y).hom ∧
            IsIso e := sorry
