module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.FormalGlueing
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- 81.10.6.1: the canonical functor QCoh(𝒪_X) ⟶ QCoh(Y → X, Z) sending F to
(F|_U, f^* F, can), where QCoh(Y → X, Z) is the category of triples (H, G, φ)
with H quasi-coherent on U = X \ Z, G quasi-coherent on Y, and
φ : (f|_V)^* H ≅ G|_V on V = Y \ f⁻¹Z.
The standing source situation assumes f quasi-compact and quasi-separated, i a
closed immersion of finite presentation, f⁻¹Z → Z an isomorphism, and f flat at
every point of f⁻¹Z. This canonical construction already exists for any f and
closed immersion i. -/
@[stacks 0AEW] #check
  (AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing.functor :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X),
      [IsClosedImmersion i] → QCoh X ⥤
        AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing.category f i)
