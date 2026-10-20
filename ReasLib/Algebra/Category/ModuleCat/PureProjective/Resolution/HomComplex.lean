module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import ReasLib.Algebra.Category.ModuleCat.PureProjective.Resolution
public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.Module

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace ModuleCat.PureProjectiveResolution

variable {A : Type u} [CommRing A]
variable {M : ModuleCat.{v} A}

/-- The integer-indexed cochain complex obtained by extending a pure projective resolution. -/
noncomputable def cochainComplex (P : ModuleCat.PureProjectiveResolution M) :
    CochainComplex (ModuleCat.{v} A) ℤ :=
  P.complex.extend ComplexShape.embeddingDownNat

/-- The module-valued Hom complex from a pure projective resolution to a module concentrated in
degree zero. -/
noncomputable def homComplex (P : ModuleCat.PureProjectiveResolution M)
    (N : ModuleCat.{v} A) : CochainComplex (ModuleCat.{v} A) ℤ :=
  CochainComplex.HomComplex.moduleComplex A P.cochainComplex
    ((CochainComplex.singleFunctor (ModuleCat.{v} A) 0).obj N)

end ModuleCat.PureProjectiveResolution
