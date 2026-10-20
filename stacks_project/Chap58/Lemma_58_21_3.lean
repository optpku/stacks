/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.RegularLocal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped ENat

universe u

/- Source erratum for clause (2): a finite normal algebra can have components
supported at the closed point. For example, A → A × ResidueField A restricts to
the identity over the punctured spectrum but is not étale over Spec A. Thus the
unrestricted algebraic clause needs correction: Module.IsTorsionFree A B excludes
these components, as in the project's normal punctured-cover API. The corrected
clause below includes this hypothesis explicitly. -/

/- Lemma 58.21.3 (1): purity holds for a regular local ring of Krull dimension at
least two: every finite étale cover of its punctured spectrum extends over Spec A. -/
@[stacks 0BMA] #check
  (AlgebraicGeometry.PuncturedSpectrum.hasPurity_of_regularLocalRing :
    ∀ {A : Type u} [CommRing A] [IsRegularLocalRing A] [Fact (2 ≤ ringKrullDim A)],
      AlgebraicGeometry.PuncturedSpectrum.HasPurity A)

/- Lemma 58.21.3 (2): the corrected finite-normal algebra criterion, with the
torsion-free hypothesis excluding components supported at the closed point. -/
@[stacks 0BMA] #check
  (AlgebraicGeometry.PuncturedSpectrum.etale_of_finite_normal :
    ∀ {A B : Type u} [CommRing A] [IsRegularLocalRing A] [CommRing B]
      [Algebra A B] [Module.Finite A B] [IsNormalRing B] [Module.IsTorsionFree A B],
      2 ≤ ringKrullDim A →
      Etale (Spec.map (CommRingCat.ofHom (algebraMap A B)) ∣_
        AlgebraicGeometry.PuncturedSpectrum.puncturedOpen A) →
      Etale (Spec.map (CommRingCat.ofHom (algebraMap A B))))
