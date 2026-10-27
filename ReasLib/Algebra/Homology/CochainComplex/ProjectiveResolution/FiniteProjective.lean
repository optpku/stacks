/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.ProjectiveResolution.Basic
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise.FiniteProjective
public import ReasLib.Algebra.Homology.CochainComplex.Bounded
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projective-minus models from termwise finite projectivity

This leaf packages a supplied bounded-above termwise finite-projective complex as a projective
model, so downstream statements do not rebuild temporary instances or repeat the `Minus.TermsIn`
constructor. The citation to Stacks `0643` is contextual: its projective resolutions have a
bounded-above projective source. A comparison map and its quasi-isomorphism proof are separate data.
@stack 0643
-/

@[expose] public section

universe u

open CategoryTheory

namespace CochainComplex.ProjectiveMinus

variable {R : Type u} [CommRing R]

/-- Package a supplied bounded-above termwise finite-projective module complex as a
`ProjectiveMinus` model, in the context of Stacks `0643`. -/
@[stacks 0643 "contextual bounded-above projective source packaging from finite projectivity"]
noncomputable def ofFiniteProjective
    (P : CochainComplex (ModuleCat R) ℤ)
    (hP : CochainComplex.minus (ModuleCat R) P)
    (hPfp : P.IsTermwiseFiniteProjective) :
    CochainComplex.ProjectiveMinus (ModuleCat R) :=
  ⟨⟨P, hP⟩, hPfp.projectiveObject⟩

/-- The finite-free specialization of the contextual bounded-above projective model packaging
in `ofFiniteProjective` (Stacks `0643`). -/
@[stacks 0643 "contextual bounded-above projective source packaging from finite freeness"]
noncomputable def ofFiniteFree
    (P : CochainComplex (ModuleCat R) ℤ)
    (hP : CochainComplex.minus (ModuleCat R) P)
    (hPfree : P.IsTermwiseFiniteFree) :
    CochainComplex.ProjectiveMinus (ModuleCat R) :=
  ofFiniteProjective P hP
    (HomologicalComplex.IsTermwiseFiniteProjective.of_finiteFree hPfree)

end CochainComplex.ProjectiveMinus
