/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.FiniteProjective
public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.Bounded
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Closed.ModuleCat.Iterated
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise.FiniteProjective

/-!
# Finite-support isomorphisms for the iterated Hom comparison

The tensor-to-iterated-Hom comparison is an isomorphism when its tensor factor is a bounded
finite-projective complex.  A second criterion records the asymmetric boundedness needed for the
same conclusion with a bounded-above termwise finite-free tensor factor: the middle complex is
bounded below and the target complex is bounded above.
@stack 0A60
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace CategoryTheory.CochainComplex.InternalHom.Module.Iterated

variable {R : Type u} [CommRing R]

/-- A bounded finite-projective tensor factor makes the tensor-to-iterated-Hom comparison an
isomorphism for arbitrary middle and target complexes. -/
@[stacks 0A60 "bounded finite-projective iterated Hom comparison"]
instance isIso_of_boundedFiniteProjective
    (K L M : CochainComplex (ModuleCat R) ℤ) [K.IsBoundedFiniteProjective] :
    IsIso (InternalHom.Module.iterated K L M) := sorry

/-- A bounded-above termwise finite-projective tensor factor gives an iterated-Hom isomorphism
when the middle complex is bounded below and the target complex is bounded above. -/
@[stacks 0A60 "finite-projective finite-support iterated Hom comparison"]
theorem isIso_of_finiteProjective_of_bounds
    (K L M : CochainComplex (ModuleCat R) ℤ)
    (hKfp : K.IsTermwiseFiniteProjective)
    (hK : CochainComplex.minus (ModuleCat R) K)
    (hL : CochainComplex.plus (ModuleCat R) L)
    (hM : CochainComplex.minus (ModuleCat R) M) :
    IsIso (InternalHom.Module.iterated K L M) := sorry

/-- A bounded-above termwise finite-free tensor factor gives an iterated-Hom isomorphism when the
middle complex is bounded below and the target complex is bounded above. -/
@[stacks 0A60 "finite-free finite-support iterated Hom comparison"]
theorem isIso_of_finiteFree_of_bounds
    (K L M : CochainComplex (ModuleCat R) ℤ) [K.IsTermwiseFiniteFree]
    (hK : CochainComplex.minus (ModuleCat R) K)
    (hL : CochainComplex.plus (ModuleCat R) L)
    (hM : CochainComplex.minus (ModuleCat R) M) :
    IsIso (InternalHom.Module.iterated K L M) := sorry

end CategoryTheory.CochainComplex.InternalHom.Module.Iterated
