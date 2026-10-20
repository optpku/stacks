/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GeneralLinear.Torsor
public import ReasLib.AlgebraicGeometry.GroupScheme.Torsor.Counterexamples
public import ReasLib.AlgebraicGeometry.GroupScheme.Torsor.Field
public import ReasLib.AlgebraicGeometry.GroupScheme.Torsor.Representability

@[expose] public section

open CategoryTheory

universe u

/- Remark 39.11.5 (1): in general, a surjective pseudo-torsor under a group
scheme need not be an fpqc torsor. -/
@[stacks 049C] #check
  (AlgebraicGeometry.GroupScheme.existsSurjectivePseudoNotTorsor :
    ∃ (S : AlgebraicGeometry.Scheme.{u}) (G : Grp (Over S))
      (X : Mod (Over S) G.X),
      Mod.IsPseudoTorsor X ∧ AlgebraicGeometry.Surjective X.X.hom ∧
        ¬ AlgebraicGeometry.GroupScheme.IsTorsor G X)

/- Remark 39.11.5 (2): in general, an fppf torsor under the sheaf represented
by a group scheme need not have representable carrier. -/
@[stacks 049C] #check
  (AlgebraicGeometry.GroupScheme.existsNonrepresentableFppfTorsor :
    ∃ (S : AlgebraicGeometry.Scheme.{u}) (G : Grp (Over S))
      (P : Sheaf.Torsor
        (AlgebraicGeometry.GroupScheme.representableGroup
          .fppf G)),
      ¬ P.carrier.1.IsRepresentable)

/- Remark 39.11.5 (3): in general, an fpqc group-scheme torsor need not be
fppf-locally trivial. -/
@[stacks 049C] #check
  (AlgebraicGeometry.GroupScheme.existsTorsorNotFppf :
    ∃ (S : AlgebraicGeometry.Scheme.{u}) (G : Grp (Over S))
      (X : Mod (Over S) G.X),
      AlgebraicGeometry.GroupScheme.IsTorsor G X ∧
        ¬ AlgebraicGeometry.GroupScheme.IsStandardTorsor G X .fppf)

/- Remark 39.11.5 (4): over the spectrum of a field, every surjective
pseudo-torsor is an fpqc torsor. -/
@[stacks 049C] #check
  (AlgebraicGeometry.GroupScheme.ofSurjectiveOverField :
    ∀ {k : Type u} [Field k]
      (G : Grp (Over (AlgebraicGeometry.Spec (CommRingCat.of k))))
      (X : Mod (Over (AlgebraicGeometry.Spec (CommRingCat.of k))) G.X)
      [AlgebraicGeometry.Surjective X.X.hom] [Mod.IsPseudoTorsor X],
      AlgebraicGeometry.GroupScheme.IsTorsor G X)

/- Remark 39.11.5 (5): an fppf sheaf torsor under an affine group scheme is
representable. -/
@[stacks 049C] #check
  (AlgebraicGeometry.GroupScheme.representableOfAffine :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : Grp (Over S))
      [AlgebraicGeometry.IsAffineHom G.X.hom]
      (P : Sheaf.Torsor
        (AlgebraicGeometry.GroupScheme.representableGroup .fppf G)),
      P.carrier.1.IsRepresentable)

/- Remark 39.11.5 (6): every torsor under `GL n` over `S` is already
Zariski-locally trivial. -/
@[stacks 049C] #check
  (AlgebraicGeometry.GroupScheme.generalLinearLocallyTrivial :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (n : ℕ)
      (X : Mod (Over S)
        (AlgebraicGeometry.GeneralLinear.baseChange
          (AlgebraicGeometry.specULiftZIsTerminal.from S) (ULift.{u} (Fin n))).X)
      (hX : AlgebraicGeometry.GroupScheme.IsTorsor
        (AlgebraicGeometry.GeneralLinear.baseChange
          (AlgebraicGeometry.specULiftZIsTerminal.from S) (ULift.{u} (Fin n))) X),
      AlgebraicGeometry.GroupScheme.IsLocallyTrivial
        (AlgebraicGeometry.GeneralLinear.baseChange
          (AlgebraicGeometry.specULiftZIsTerminal.from S) (ULift.{u} (Fin n))) X)
