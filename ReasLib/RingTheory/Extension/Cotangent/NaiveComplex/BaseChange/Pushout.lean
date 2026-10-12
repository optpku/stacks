/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.TensorProduct
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude
public import ReasLib.Algebra.Homology.Embedding.Functor
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.BaseChange.Derived
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.ExtendScalars
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pushout base change for naive cotangent complexes

@stack 0FJU

For the canonical pushout `A' ⊗[A] B`, this file owns the chain-level comparison from the
termwise scalar extension of `NL{B⁄A}` to `NL{A' ⊗[A] B⁄A'}` and its derived counterpart.
-/

@[expose] public section

noncomputable section

open CategoryTheory ComplexShape
open scoped DerivedTensorWithAlgebra NaiveCotangent TensorProduct

universe u

namespace Algebra.NaiveCotangent.Pushout

variable (A A' B : Type u)
variable [CommRing A] [CommRing A'] [CommRing B]
variable [Algebra A A'] [Algebra A B]

local notation "B'" => A' ⊗[A] B

-- Local instance justification (instance diamond): expose both canonical tensor-factor algebra
-- structures only in this pushout leaf, avoiding competing global instances.
attribute [local instance] Algebra.TensorProduct.leftAlgebra Algebra.TensorProduct.rightAlgebra

/-- The ordinary scalar extension of `NL{B⁄A}` to the canonical pushout ring. -/
@[stacks 0FJU "underived pushout base-change object"]
noncomputable abbrev underivedBaseChangeObject :
    DerivedCategory (ModuleCat B') :=
  DerivedCategory.Q.obj
    (((ModuleCat.extendScalars (algebraMap B B')).mapHomologicalComplex (up ℤ)).obj
      ((NL{B⁄A}).extend embeddingDownNat))

/-- The canonical chain-level map from the scalar extension of the self-presentation of `B` over
`A` to the self-presentation of the pushout over `A'`. -/
@[stacks 0FJU "canonical chain-level pushout comparison"]
noncomputable def chainMap :
    Extension.NaiveCotangent.ExtendScalars.source
        ((Generators.self A B : Generators A B B).toExtension) ⟶
      Extension.NaiveCotangent.complex
        ((Generators.self A' B' : Generators A' B' B').toExtension) :=
  let P : Generators A B B := Generators.self A B
  let Q : Generators A' B' B' := Generators.self A' B'
  Extension.NaiveCotangent.ExtendScalars.map
    (Generators.defaultHom P Q).toExtensionHom

/-- The canonical cochain map obtained from `chainMap` by extension from `ℕ` to `ℤ`. -/
@[stacks 0FJU "canonical cochain-level pushout comparison"]
noncomputable def cochainMap :
    ((ModuleCat.extendScalars (algebraMap B B')).mapHomologicalComplex (up ℤ)).obj
        ((NL{B⁄A}).extend embeddingDownNat) ⟶
      (NL{B'⁄A'}).extend embeddingDownNat :=
  letI : (ModuleCat.extendScalars.{u, u, u} (algebraMap B B')).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (algebraMap B B')).left_adjoint_additive
  (ComplexShape.Embedding.mapAppIso embeddingDownNat
      (ModuleCat.extendScalars (algebraMap B B')) NL{B⁄A}).hom ≫
    HomologicalComplex.extendMap (chainMap A A' B) embeddingDownNat

/-- The canonical underived pushout comparison
`NL{B⁄A} ⊗[B] B' ⟶ NL{B'⁄A'}` in `D(B')`. -/
@[stacks 0FJU "canonical underived pushout comparison"]
noncomputable def underivedComparison :
    underivedBaseChangeObject A A' B ⟶ Algebra.naiveCotangentObject A' B' :=
  DerivedCategory.Q.map (cochainMap A A' B)

/-- The canonical derived pushout comparison
`NL{B⁄A} ⊗[B]^L[B'] ⟶ NL{B'⁄A'}` in `D(B')`. -/
@[stacks 0FJU "canonical derived pushout comparison"]
noncomputable def derivedComparison :
    (Algebra.naiveCotangentObject A B ⊗[B]^L[B']) ⟶
      Algebra.naiveCotangentObject A' B' :=
  DerivedBaseChange.selfComparison (R := A) (S := B) (S' := B') ≫
    underivedComparison A A' B

/-- Lemma 15.86.3 (1) (0FJU): if `B` is flat over `A`, the canonical underived pushout
comparison is an isomorphism. -/
@[stacks 0FJU "(1), flat underived pushout comparison"]
theorem underivedComparison_isIso_of_flat [Module.Flat A B] :
    IsIso (underivedComparison A A' B) := sorry
/- Proof strategy: compute both sides from the self-presentation of `B/A`.  Flatness of `B` over
`A` makes relation modules and Kähler differentials commute with the tensor-product pushout, so
`cochainMap` is a quasi-isomorphism; apply `DerivedCategory.Q.map_isIso`. -/

/-- Lemma 15.86.3 (2) (0FJU): if `B` is flat over `A` and `NL{B⁄A}` has Tor-amplitude in
`[-1, 0]`, the canonical derived pushout comparison is an isomorphism. -/
@[stacks 0FJU "(2), flat derived pushout comparison"]
theorem derivedComparison_isIso_of_flat_of_hasTorAmplitudeIn
    [Module.Flat A B]
    (hNL : DerivedCategory.HasTorAmplitudeIn
      (R := B) (Algebra.naiveCotangentObject A B) (-1) 0) :
    IsIso (derivedComparison A A' B) := sorry
/- Proof strategy: factor `derivedComparison` as `DerivedBaseChange.selfComparison` followed by
`underivedComparison`.  The latter is an isomorphism by flatness; the Tor-amplitude bound upgrades
the truncated derived-to-underived comparison to an isomorphism on the full two-term object, so
the composite is an isomorphism. -/

end Algebra.NaiveCotangent.Pushout
