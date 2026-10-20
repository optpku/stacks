module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.AlgHom.Factorisation
public import ReasLib.RingTheory.Smooth.SingularLocus

@[expose] public section

/-!
# Base-ideal control on finite factorisations

This leaf owns finite-presentation factorisations whose midpoint singular
ideal contains the extension of a prescribed ideal of the base ring.
-/

universe u v w

namespace AlgHom.Factorisation.Finite

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

/-- A finite factorisation with singular-ideal control by an ideal of the
base ring. -/
@[stacks 07CR "finite factorisation with base-ideal control"]
structure BaseControl (f : A →ₐ[R] B) (I : Ideal R) where
  /-- The underlying finite-presentation factorisation. -/
  base : AlgHom.Factorisation.Finite f
  /-- The extended base ideal lies in the singular ideal of the midpoint. -/
  singularIdeal_le :
    Ideal.map (algebraMap R base.mid) I ≤ Algebra.singularIdeal R base.mid

namespace BaseControl

variable {f : A →ₐ[R] B} {I J : Ideal R}

/-- The finitely presented midpoint of a base-controlled factorisation. -/
abbrev mid (F : BaseControl f I) := F.base.mid

/-- The source map of a base-controlled factorisation. -/
noncomputable abbrev fromSource (F : BaseControl f I) : A →ₐ[R] F.mid :=
  F.base.fromSource

/-- The target map of a base-controlled factorisation. -/
noncomputable abbrev toTarget (F : BaseControl f I) : F.mid →ₐ[R] B :=
  F.base.toTarget

/-- Attach base-ideal control to a finite factorisation. -/
def of (F : AlgHom.Factorisation.Finite f)
    (hI : Ideal.map (algebraMap R F.mid) I ≤ Algebra.singularIdeal R F.mid) :
    BaseControl f I where
  base := F
  singularIdeal_le := hI

/-- Forgetting the control attached by `of` recovers the supplied finite
factorisation. -/
@[simp]
theorem base_of (F : AlgHom.Factorisation.Finite f)
    (hI : Ideal.map (algebraMap R F.mid) I ≤ Algebra.singularIdeal R F.mid) :
    (of F hI).base = F := sorry

/-- Attach base-ideal control to a factorisation with a finitely presented
midpoint. -/
def ofFactorisation (F : f.Factorisation)
    [Algebra.FinitePresentation R F.mid]
    (hI : Ideal.map (algebraMap R F.mid) I ≤ Algebra.singularIdeal R F.mid) :
    BaseControl f I :=
  of (AlgHom.Factorisation.Finite.of F) hI

/-- Build a base-controlled factorisation directly from its midpoint maps. -/
noncomputable def ofMaps
    {C : Type (max u v w)} [CommRing C] [Algebra R C]
    [Algebra.FinitePresentation R C]
    (g : A →ₐ[R] C) (h : C →ₐ[R] B) (hfactor : h.comp g = f)
    (hI : Ideal.map (algebraMap R C) I ≤ Algebra.singularIdeal R C) :
    BaseControl f I :=
  of (AlgHom.Factorisation.Finite.ofMaps g h hfactor) hI

/-- The source projection of a directly constructed controlled
factorisation is the supplied source map. -/
@[simp]
theorem fromSource_ofMaps
    {C : Type (max u v w)} [CommRing C] [Algebra R C]
    [Algebra.FinitePresentation R C]
    (g : A →ₐ[R] C) (h : C →ₐ[R] B) (hfactor : h.comp g = f)
    (hI : Ideal.map (algebraMap R C) I ≤ Algebra.singularIdeal R C) :
    (ofMaps g h hfactor hI).fromSource = g := sorry

/-- The target projection of a directly constructed controlled
factorisation is the supplied target map. -/
@[simp]
theorem toTarget_ofMaps
    {C : Type (max u v w)} [CommRing C] [Algebra R C]
    [Algebra.FinitePresentation R C]
    (g : A →ₐ[R] C) (h : C →ₐ[R] B) (hfactor : h.comp g = f)
    (hI : Ideal.map (algebraMap R C) I ≤ Algebra.singularIdeal R C) :
    (ofMaps g h hfactor hI).toTarget = h := sorry

/-- Restricting the controlled ideal preserves its singular-ideal
containment. -/
theorem singularIdeal_le_ofLE (F : BaseControl f I) (hJI : J ≤ I) :
    Ideal.map (algebraMap R F.mid) J ≤ Algebra.singularIdeal R F.mid := sorry

/-- Base-ideal control is contravariant in the controlled ideal. -/
def ofLE (F : BaseControl f I) (hJI : J ≤ I) : BaseControl f J :=
  of F.base (F.singularIdeal_le_ofLE hJI)

/-- The finite presentation, triangle, and base-ideal containment carried by
a base-controlled factorisation. -/
theorem spec (F : BaseControl f I) :
    Algebra.FinitePresentation R F.mid ∧
      F.toTarget.comp F.fromSource = f ∧
      Ideal.map (algebraMap R F.mid) I ≤ Algebra.singularIdeal R F.mid := sorry

end BaseControl

end AlgHom.Factorisation.Finite
