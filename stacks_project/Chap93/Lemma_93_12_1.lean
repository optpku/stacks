module

public import ReasLib.Algebra.Homology.DerivedCategory.NilpotentLift
import StacksCheckRecall

/-!
# Flat lifts versus bounded-above derived lifts
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct Algebra.TensorProduct.Right

universe u

/- Lemma 93.12.1: for a surjection `A' → A` of commutative rings with nilpotent kernel, a
flat map `A' → P'`, `P := P' ⊗[A'] A`, and an `A`-flat `P`-module `M`, existence of an
`A'`-flat `P'`-module `M'` with `M' ⊗[P'] P ≅ M` is equivalent to existence of
`K' ∈ D⁻(ModuleCat P')` with `K' ⊗[P']^L P ≅ single0 M`. -/
@[stacks 0DZ1]
#check (CategoryTheory.ModuleCat.NilpotentLift.existsFlatLift_iff_existsBoundedAboveDerivedLift :
  ∀ {A' A P' : Type u} [CommRing A'] [CommRing A] [CommRing P']
    [Algebra A' A] [Algebra A' P'] [Module.Flat A' P']
    (hsurj : Function.Surjective (algebraMap A' A))
    (hker : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (M : ModuleCat.{u} (P' ⊗[A'] A))
    (hMflat : Module.Flat A
      ((ModuleCat.restrictScalars (algebraMap A (P' ⊗[A'] A))).obj M)),
    ModuleCat.NilpotentLift.existsFlatLift A' P' M ↔
      ModuleCat.NilpotentLift.existsBoundedAboveDerivedLift P' M)

end
