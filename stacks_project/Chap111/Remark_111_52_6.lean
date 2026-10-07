module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.EulerCharacteristic

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Remark 111.52.6: given a projective scheme X over a field k, with structure morphism
f : X ⟶ Spec (CommRingCat.of k) (hence proper), and a coherent sheaf F on X, the Euler
characteristic χ(X, F) is Scheme.Hom.eulerCharacteristic f F, the signed finite sum
∑ᶠ i, (-1)^i dim_k H^i(X, F). -/
@[stacks 02B1] #check
  (AlgebraicGeometry.Scheme.Hom.eulerCharacteristic :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (F : X.Modules) [F.IsCoherent], ℤ)

#check
  (AlgebraicGeometry.Scheme.Hom.eulerCharacteristic_def :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (F : X.Modules) [F.IsCoherent],
      AlgebraicGeometry.Scheme.Hom.eulerCharacteristic f F =
        ∑ᶠ i : ℕ,
          ((i : ℤ).negOnePow : ℤ) *
            (AlgebraicGeometry.Scheme.Hom.cohomologyFinrank f F i : ℤ))
