module

public import ReasLib.Algebra.Homology.CochainComplex.ProjectiveResolution.Basic
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise.FiniteProjective
public import ReasLib.Algebra.Homology.CochainComplex.Bounded
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projective-minus models from termwise finite projectivity

Finite projectivity is the source-facing hypothesis most often used to build a bounded-above
projective model.  This leaf packages that construction once, so downstream statements do not
rebuild temporary instances or repeat the `Minus.TermsIn` constructor.
@stack 0A60
-/

@[expose] public section

universe u

open CategoryTheory

namespace CochainComplex.ProjectiveMinus

variable {R : Type u} [CommRing R]

/-- Package a bounded-above termwise finite-projective module complex as a `ProjectiveMinus` object. -/
@[stacks 0A60 "finite-projective projective-minus model"]
noncomputable def ofFiniteProjective
    (P : CochainComplex (ModuleCat R) ℤ)
    (hP : CochainComplex.minus (ModuleCat R) P)
    (hPfp : P.IsTermwiseFiniteProjective) :
    CochainComplex.ProjectiveMinus (ModuleCat R) :=
  ⟨⟨P, hP⟩, hPfp.projectiveObject⟩

/-- The finite-free specialization of `ofFiniteProjective`. -/
@[stacks 0A60 "finite-free projective-minus model"]
noncomputable def ofFiniteFree
    (P : CochainComplex (ModuleCat R) ℤ)
    (hP : CochainComplex.minus (ModuleCat R) P)
    (hPfree : P.IsTermwiseFiniteFree) :
    CochainComplex.ProjectiveMinus (ModuleCat R) :=
  ofFiniteProjective P hP
    (HomologicalComplex.IsTermwiseFiniteProjective.of_finiteFree hPfree)

end CochainComplex.ProjectiveMinus
