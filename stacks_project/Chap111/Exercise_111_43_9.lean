/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Sections
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {A : Type u} [CommRing A]

/- Exercise 111.43.9: for a finitely generated ideal I of A and an A-module M whose I-torsion
vanishes, the canonical comparison colimit (I.powerHomModuleDiagram M) ⟶
idealComplementTildeSections I M is an isomorphism. Here U is Spec A \ V(I), H⁰(U, tilde M)
is identified with those complement sections, and vanishing I-torsion is the annihilator
condition that a • x = 0 for every a ∈ I implies x = 0. -/
@[stacks 0DAS] #check
  (AlgebraicGeometry.Scheme.Modules.isIso_idealPowerHomColimitToComplementSections_of_annihilatorCondition :
    ∀ (I : Ideal A) (hI : I.FG) (M : ModuleCat A),
      (∀ x : M, (∀ a : A, a ∈ I → a • x = 0) → x = 0) →
        IsIso (AlgebraicGeometry.Scheme.Modules.idealPowerHomColimitToComplementSections
          I hI M))

end AlgebraicGeometry.Scheme.Modules
