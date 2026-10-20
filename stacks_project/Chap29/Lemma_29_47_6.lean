/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.Seminormalization

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 29.47.6 (1): The category of ring maps `A → B` inducing a universal homeomorphism on
spectra has a final object. -/
@[stacks 0EUR] #check
  (AlgebraicGeometry.instHasTerminalAbsoluteWeakNormalizationAlgebras :
    ∀ (A : Type u) [CommRing A],
      HasTerminal (AlgebraicGeometry.AbsoluteWeakNormalizationAlgebras A))

/- Lemma 29.47.6 (2): For an object `A → B` of that category, the map from `B` to the final
object is an isomorphism exactly when `B` is absolutely weakly normal. -/
@[stacks 0EUR] #check
  (AlgebraicGeometry.isIso_to_absoluteWeakNormalization_iff_absolutelyWeaklyNormalRing :
    ∀ (A : Type u) [CommRing A]
      (B : AlgebraicGeometry.AbsoluteWeakNormalizationAlgebras A),
      IsIso (terminal.from B :
        B ⟶ ⊤_ (AlgebraicGeometry.AbsoluteWeakNormalizationAlgebras A)) ↔
        AbsolutelyWeaklyNormalRing (B.1 : Type u))

/- Lemma 29.47.6 (3): The category of ring maps `A → B` inducing a universal homeomorphism on
spectra and isomorphisms on residue fields has a final object. -/
@[stacks 0EUR] #check
  (AlgebraicGeometry.instHasTerminalSeminormalizationAlgebras :
    ∀ (A : Type u) [CommRing A],
      HasTerminal (AlgebraicGeometry.SeminormalizationAlgebras A))

/- Lemma 29.47.6 (4): For an object `A → B` of that category, the map from `B` to the final
object is an isomorphism exactly when `B` is seminormal. -/
@[stacks 0EUR] #check
  (AlgebraicGeometry.isIso_to_seminormalization_iff_seminormalRing :
    ∀ (A : Type u) [CommRing A] (B : AlgebraicGeometry.SeminormalizationAlgebras A),
      IsIso (terminal.from B : B ⟶ ⊤_ (AlgebraicGeometry.SeminormalizationAlgebras A)) ↔
        SeminormalRing (B.1 : Type u))

/- Lemma 29.47.6 (5): Every ring map `φ : A → A'` induces a unique compatible map between the
terminal absolute weak normalizations. -/
@[stacks 0EUR] #check
  (AlgebraicGeometry.existsUnique_absoluteWeakNormalizationMap :
    ∀ {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A'),
      ∃! φawn :
          ((⊤_ (AlgebraicGeometry.AbsoluteWeakNormalizationAlgebras A)).1 : Type u) →+*
            ((⊤_ (AlgebraicGeometry.AbsoluteWeakNormalizationAlgebras A')).1 : Type u),
        φawn.comp
            (algebraMap A
              ((⊤_ (AlgebraicGeometry.AbsoluteWeakNormalizationAlgebras A)).1 : Type u)) =
          (algebraMap A'
              ((⊤_ (AlgebraicGeometry.AbsoluteWeakNormalizationAlgebras A')).1 : Type u)).comp φ)

/- Lemma 29.47.6 (6): Every ring map `φ : A → A'` induces a unique compatible map between the
terminal seminormalizations. -/
@[stacks 0EUR] #check
  (AlgebraicGeometry.existsUnique_seminormalizationMap :
    ∀ {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A'),
      ∃! φsn :
          ((⊤_ (AlgebraicGeometry.SeminormalizationAlgebras A)).1 : Type u) →+*
            ((⊤_ (AlgebraicGeometry.SeminormalizationAlgebras A')).1 : Type u),
        φsn.comp
            (algebraMap A
              ((⊤_ (AlgebraicGeometry.SeminormalizationAlgebras A)).1 : Type u)) =
          (algebraMap A'
              ((⊤_ (AlgebraicGeometry.SeminormalizationAlgebras A')).1 : Type u)).comp φ)
