/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Differentials.Uniformizer
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.RingedSpace.Hom
open TopCat.Sheaf.RelativeDifferentials.Stalk
open scoped AlgebraicGeometry

universe u

/- Lemma 53.12.3 -/
@[stacks 0C1E] #check
  (AlgebraicGeometry.Scheme.Hom.uniformizerDifferential_freelyGenerates :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) (x : X)
      (h_closed : x ∈ closedPoints X) (h_smooth : f.SmoothAt x)
      (h_dim : f.fiberDimensionAt x = (1 : WithBot ℕ∞))
      [h_separable : ResidueField.IsSeparableOverSpec f x]
      (s : X.presheaf.stalk x)
      (h_uniformizer : IsLocalRing.maximalIdeal
        (X.presheaf.stalk x) = Ideal.span {s}),
      let d : X.presheaf.stalk x →
          RingedSpace.stalkModuleCat (Ω[f.toShHom]) x :=
        (derivation (inverseImageStructureSheafHomComm f.toShHom) x).d
      LinearIndependent (X.presheaf.stalk x) (fun _ : Fin 1 ↦ d s) ∧
        Submodule.span (X.presheaf.stalk x) {d s} = ⊤)
