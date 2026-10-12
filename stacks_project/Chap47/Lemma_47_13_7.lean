/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap47.Situation_47_13_6
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.QuasiIso.Derived.Coextension
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory
open CochainDGAlgebra.Hom
open CochainDGAlgebra.Hom.Derived
open DifferentialGradedBimodule

universe u

variable {R : Type u} [CommRing R]
variable {A : Type u} [Ring A] [Algebra R A]
variable {E : CochainDGAlgebra.{u, u} R}
variable (f : E ⟶ CochainDGAlgebra.ofAlgebra R A)
variable (hf : CochainDGAlgebra.quasiIso f)

/- Lemma 47.13.7: in Situation 47.13.6, derived `RHom_R(A, -)` is naturally
isomorphic to derived `RHom_R(E, -)` followed by the equivalence
`- ⊗ᴸ_E A : D(E) ⟶ D(A)` induced by the quasi-isomorphism `f : E ⟶ A`. -/
@[stacks 0BZC] #check
  (CochainDGAlgebra.Hom.Derived.coextensionFromBaseIsoExtension f hf :
    InternalHom.derivedFunctor
        (ChangeOfRings.restriction
          (CochainDGAlgebra.Hom.fromBase (CochainDGAlgebra.ofAlgebra R A))) ≅
      InternalHom.derivedFunctor
          (ChangeOfRings.restriction (CochainDGAlgebra.Hom.fromBase E)) ⋙
        extension f)
