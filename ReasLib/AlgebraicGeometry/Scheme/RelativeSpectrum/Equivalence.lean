/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Over
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Affine
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Properties

/-!
# Relative spectra and affine morphisms

This file states the anti-equivalence between affine morphisms over a scheme
and quasi-coherent algebras, including its compatibility with base change.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AffineMorphismOver

/-- A candidate anti-equivalence sends every affine morphism to the
quasi-coherent algebra obtained by pushing forward its structure sheaf. -/
def IsPushforwardEquivalence (S : Scheme.{u})
    (e : (AffineMorphismOver S)ᵒᵖ ≌ S.QcAlgebraUnder) : Prop :=
  ∀ T : AffineMorphismOver S,
    Nonempty
      (e.functor.obj (Opposite.op T) ≅
        Scheme.pushforwardStructureSheafQcAlgebra T.obj.hom)

/-- The pushforward condition for an anti-equivalence holds exactly when it
holds objectwise for every affine morphism over the base. -/
theorem isPushforwardEquivalence_iff (S : Scheme.{u})
    (e : (AffineMorphismOver S)ᵒᵖ ≌ S.QcAlgebraUnder) :
    IsPushforwardEquivalence S e ↔
      ∀ T : AffineMorphismOver S,
        Nonempty
          (e.functor.obj (Opposite.op T) ≅
            Scheme.pushforwardStructureSheafQcAlgebra T.obj.hom) :=
  Iff.rfl

/-- Affine morphisms over a scheme are anti-equivalent to quasi-coherent
algebras, with the equivalence given objectwise by pushforward of structure sheaves. -/
theorem exists_pushforwardEquivalence (S : Scheme.{u}) :
    ∃ e : (AffineMorphismOver S)ᵒᵖ ≌ S.QcAlgebraUnder,
      IsPushforwardEquivalence S e := sorry

/-- A pushforward anti-equivalence is compatible with base change if every
base morphism admits a pushforward anti-equivalence over the new base, an
explicit pullback functor on quasi-coherent algebras, and a comparison
isomorphism. -/
def IsBaseChangeCompatible (S : Scheme.{u})
    (eS : (AffineMorphismOver S)ᵒᵖ ≌ S.QcAlgebraUnder) : Prop :=
  IsPushforwardEquivalence S eS ∧
    ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
      ∃ (eS' : (AffineMorphismOver S')ᵒᵖ ≌ S'.QcAlgebraUnder)
        (F : S.QcAlgebraUnder ⥤ S'.QcAlgebraUnder)
        (_ : ∀ A, Scheme.RelativeSpectrumPullback g A (F.obj A)),
        IsPushforwardEquivalence S' eS' ∧
          Nonempty ((baseChange g).op ⋙ eS'.functor ≅ eS.functor ⋙ F)

/-- Base-change compatibility consists exactly of the objectwise pushforward
condition and compatible anti-equivalence, pullback, and comparison data after
every base change. -/
theorem isBaseChangeCompatible_iff (S : Scheme.{u})
    (eS : (AffineMorphismOver S)ᵒᵖ ≌ S.QcAlgebraUnder) :
    IsBaseChangeCompatible S eS ↔
      IsPushforwardEquivalence S eS ∧
        ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
          ∃ (eS' : (AffineMorphismOver S')ᵒᵖ ≌ S'.QcAlgebraUnder)
            (F : S.QcAlgebraUnder ⥤ S'.QcAlgebraUnder)
            (_ : ∀ A, Scheme.RelativeSpectrumPullback g A (F.obj A)),
            IsPushforwardEquivalence S' eS' ∧
              Nonempty ((baseChange g).op ⋙ eS'.functor ≅ eS.functor ⋙ F) :=
  Iff.rfl

/-- Every scheme admits a pushforward anti-equivalence between affine
morphisms over it and quasi-coherent algebras that is compatible with
arbitrary base change. -/
theorem exists_baseChangeCompatiblePushforwardEquivalence (S : Scheme.{u}) :
    ∃ eS : (AffineMorphismOver S)ᵒᵖ ≌ S.QcAlgebraUnder,
      IsBaseChangeCompatible S eS := sorry

end AlgebraicGeometry.AffineMorphismOver
