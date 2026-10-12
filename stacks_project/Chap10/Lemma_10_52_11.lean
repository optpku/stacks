/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.CompositionSeries.Localization
import StacksCheckRecall

/-!
# Composition factors and localized length

Lemma 10.52.11 identifies the simple factors of a composition series, their maximal
annihilators, and their multiplicities after localization.

@stack 00J3
-/

@[expose] public section

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Lemma 10.52.11 (1) (00J3): the number of factors in a composition series from `⊥` to
`⊤` is the length of the ambient module. -/
@[stacks 00J3 "(1)"]
#check (Module.length_compositionSeries (R := R) (M := M) :
  ∀ (s : CompositionSeries (Submodule R M)),
    s.head = ⊥ → s.last = ⊤ → s.length = Module.length R M)

/- Lemma 10.52.11 (2) (00J3): every successive composition factor is simple. -/
@[stacks 00J3 "(2)"]
#check (Module.CompositionSeries.Factor.isSimple (R := R) (M := M) :
  ∀ (s : CompositionSeries (Submodule R M)) (i : Fin s.length),
    IsSimpleModule R (Module.CompositionSeries.factor s i))

/- Lemma 10.52.11 (3) (00J3): the annihilator of every composition factor is maximal. -/
@[stacks 00J3 "(3), maximal annihilator"]
#check (Module.CompositionSeries.Factor.annihilatorIsMaximal (R := R) (M := M) :
  ∀ (s : CompositionSeries (Submodule R M)) (i : Fin s.length),
    (Module.annihilator R (Module.CompositionSeries.factor s i)).IsMaximal)

/- Lemma 10.52.11 (3) (00J3): every composition factor is the quotient by its canonical maximal
annihilator. -/
@[stacks 00J3 "(3), quotient presentation"]
#check (Module.CompositionSeries.Factor.nonemptyLinearEquivQuotientAnnihilator
    (R := R) (M := M) :
  ∀ (s : CompositionSeries (Submodule R M)) (i : Fin s.length),
    Nonempty (Module.CompositionSeries.factor s i ≃ₗ[R]
      R ⧸ Module.annihilator R (Module.CompositionSeries.factor s i)))

/- Lemma 10.52.11 (4) (00J3): the multiplicity of a maximal ideal among the factors equals the
length of the localized module. -/
@[stacks 00J3 "(4)"]
#check (Module.CompositionSeries.multiplicity_eq_length_localized (R := R) (M := M) :
  ∀ (s : CompositionSeries (Submodule R M)),
    s.head = ⊥ → s.last = ⊤ → ∀ (m : MaximalSpectrum R),
      (Module.CompositionSeries.multiplicity s m : ℕ∞) =
        Module.length (Localization.AtPrime m.asIdeal)
          (LocalizedModule.AtPrime m.asIdeal M))

end
