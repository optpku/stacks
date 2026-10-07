module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.LinearSystem

/-!
# Immersions induced by linear systems

This file records when a generating linear system defines an immersion into the projective
scheme of its vector space.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem

variable {k : Type u} [Field k]
variable {V : Type u} [AddCommGroup V] [Module k V]

/-- A linear system induces an immersion when it generates the invertible module and every
projective-bundle representation makes its canonical projective morphism an immersion. -/
def InducesImmersion
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L) : Prop :=
  Generates X L ψ ∧
    ∀ (hP : Scheme.ProjectiveBundle.Representation (toSpec k V) (moduleSheaf k V))
      (hψ : Generates X L ψ),
      IsImmersion (morphism hP X L ψ hψ)

/-- Inducing an immersion is equivalent to generation together with immersion of every
canonical projective morphism obtained from the linear system. -/
theorem inducesImmersion_iff
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L) :
    InducesImmersion X L ψ ↔
      Generates X L ψ ∧
        ∀ (hP : Scheme.ProjectiveBundle.Representation (toSpec k V) (moduleSheaf k V))
          (hψ : Generates X L ψ),
          IsImmersion (morphism hP X L ψ hψ) :=
  Iff.rfl

end AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem
