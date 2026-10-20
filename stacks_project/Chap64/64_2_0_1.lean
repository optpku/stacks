/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.CompactSupport.FiniteCoefficients
import StacksCheckRecall

/-!
# 64.2.0.1 (03SK): the preliminary trace formula

Source: `trace-equation-trace-formula-initial`,
`source/stacks-official-a04446e57ec1/tex/trace.tex`, lines 36–60.

For a finite type scheme X of dimension 1 over a finite field k, a prime ℓ,
and a constructible flat Z/ℓⁿZ-sheaf F, the source first displays

  ∑ x ∈ X(k), Tr(Frob | F_x̄) = ∑ i = 0,…,2, (-1)^i Tr(π_X* | H_c^i(X_k̄,F)).

The equality is intended to take values in Z/ℓⁿZ. This is a preliminary
description of the formula to be developed, explicitly qualified immediately
after the display: “this formulation is slightly wrong as stated.” The more
precise display `trace-equation-trace-formula-second` is likewise introduced as
“albeit a false one”; its explanation says that the trace on the right does not
make sense for the sheaves under consideration (trace.tex, lines 294–311).

The obstruction is not that every instance of the displayed equality is false.
Even a flat finite-coefficient sheaf can have nonflat individual cohomology
modules, on which the intended module trace is unavailable. Lines 466–483 give
the Z/ℓ²Z coinvariant example and explain the remedy: traces on the total perfect
derived cohomology complex. The later rigorous trace formula is a separate
statement, with its own objects and hypotheses.

This module preserves the preliminary display and its explicit source warning
as explanatory content; it asserts no equation or negation of the equation.
Source-coverage classification is separate from mathematical success.

Classification aliases for the same source entry:
`03SK::statement_repair::1`, `03SK::statement_repair::2`.
These identify repair episodes, not additional mathematical claims.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry MonoidalCategory

universe u

/- 03SK::statement_repair::2: The source marks the displayed equality as wrong as stated;
only its geometric stalk, compact-support cohomology and Frobenius ingredients are recorded. -/
@[stacks 03SK] #check (AlgebraicGeometry.Scheme.Etale.geometricModuleStalk :
  ∀ {k : Type u} [Field k] {ℓ n : ℕ} {X : Scheme.{u}},
    Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n))) →
    (Spec (CommRingCat.of (AlgebraicClosure k)) ⟶ X) →
    ModuleCat.{u} (ZMod (ℓ ^ n)))

#check (AlgebraicGeometry.Scheme.Etale.etaleCohomologyCompactSupport :
  ∀ {k : Type u} [Field k] {ℓ n : ℕ}
    (X : SchemeOverField k)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n))))
    (i : ℕ)
    [Etale (Compactification.Of.ι P)]
    [∀ G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} (ZMod (ℓ ^ n)),
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
    [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasWeakSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasSheafify
      (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom).smallEtaleTopology
      (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [((smallEtalePullback
          (FieldExtension.toSource k (AlgebraicClosure k) P.obj.right.hom)).sheafPushforwardContinuous
        (ModuleCat.{u} (ZMod (ℓ ^ n)))
        P.obj.right.left.smallEtaleTopology
        (FieldExtension.baseChange k (AlgebraicClosure k)
          P.obj.right.hom).smallEtaleTopology).IsRightAdjoint]
    [HasWeakSheafify
      (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom).smallEtaleTopology
      (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasSheafify
      (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom).smallEtaleTopology
      AddCommGrpCat.{u}]
    [HasExt
      (Sheaf
        (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom).smallEtaleTopology
        AddCommGrpCat.{u})]
    [(FieldExtension.baseChange k (AlgebraicClosure k)
        P.obj.right.hom).smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} (ZMod (ℓ ^ n))) AddCommGrpCat.{u})],
    ModuleCat.{u} (ZMod (ℓ ^ n)))

#check AlgebraicGeometry.Scheme.Etale.geometricFrobeniusStalk
#check AlgebraicGeometry.Scheme.Etale.geometricFrobenius_cohomologyCompactSupport
