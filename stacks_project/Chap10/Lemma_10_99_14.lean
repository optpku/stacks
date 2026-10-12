/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap10.Lemma_10_99_13
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.IsTensorProduct
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Tensor
import StacksCheckRecall

/-!
# Flatness in a localized tensor-product square

@stack 00MO
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct Algebra.TensorProduct.Right

universe u

noncomputable section

namespace CategoryTheory.ModuleCat.Tor.LocalizedTensorSquare

variable {R S R' S' M : Type u}
variable [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
variable [Algebra R S] [Algebra R R'] [Algebra R S'] [Algebra S S'] [Algebra R' S']
variable [IsScalarTower R S S'] [IsScalarTower R R' S']
variable [Algebra (S ⊗[R] R') S']
variable [IsScalarTower S (S ⊗[R] R') S']
variable [IsScalarTower R' (S ⊗[R] R') S']
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- The extension `IR'` of an ideal `I` in the tensor-product square. -/
abbrev extendedIdeal (I : Ideal R) : Ideal R' :=
  Ideal.map (algebraMap R R') I

/-- The target-corner module `M' = S' ⊗[S] M`. -/
abbrev baseChangedModule : Type u :=
  S' ⊗[S] M

/-- The source `Tor_1^R(M, R / I)`. -/
abbrev source (I : Ideal R) : ModuleCat R :=
  (((CategoryTheory.Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj
    (ModuleCat.of R (R ⧸ I)))

/-- The target `Tor_1^{R'}(M', R' / IR')`. -/
abbrev target (I : Ideal R) : ModuleCat R' :=
  (((CategoryTheory.Tor' (ModuleCat R') 1).obj
      (ModuleCat.of R' (baseChangedModule (S := S) (S' := S') (M := M)))).obj
    (ModuleCat.of R' (R' ⧸ extendedIdeal (R := R) (R' := R') I)))

/-- The natural map
`Tor_1^R(M, R / I) -> Tor_1^{R'}(S' ⊗[S] M, R' / IR')`
attached to the tensor-product square. -/
@[stacks 00MO "Tor comparison"]
noncomputable def comparison (I : Ideal R) :
    source (R := R) (M := M) I ⟶
      (ModuleCat.restrictScalars (algebraMap R R')).obj
        (target (R := R) (S := S) (R' := R') (S' := S') (M := M) I) := sorry

end CategoryTheory.ModuleCat.Tor.LocalizedTensorSquare

section

variable {R S R' S' M : Type u}
variable [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
variable [Algebra R S] [Algebra R R'] [Algebra R S'] [Algebra S S'] [Algebra R' S']
variable [IsScalarTower R S S'] [IsScalarTower R R' S']
variable [Algebra (S ⊗[R] R') S']
variable [IsScalarTower S (S ⊗[R] R') S']
variable [IsScalarTower R' (S ⊗[R] R') S']
variable [IsLocalRing R] [IsLocalRing S] [IsLocalRing R'] [IsLocalRing S']
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [IsNoetherianRing R'] [IsNoetherianRing S']
variable [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap R R')]
variable [IsLocalHom (algebraMap S S')] [IsLocalHom (algebraMap R' S')]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
variable [Module.Finite S M]

/-- **Lemma 10.99.14** ([Stacks tag 00MO](https://stacks.math.columbia.edu/tag/00MO)):
in a localized tensor-product square, flatness modulo `I` together with vanishing of the
natural first-Tor comparison implies flatness of the base-changed module. -/
@[stacks 00MO]
theorem Module.Flat.of_localizedTensorSquare
    (W : Submonoid (S ⊗[R] R')) [IsLocalization W S']
    (I : Ideal R) (hI : I ≠ ⊤)
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
    (hzero :
      CategoryTheory.ModuleCat.Tor.LocalizedTensorSquare.comparison
        (R := R) (S := S) (R' := R') (S' := S') (M := M) I = 0) :
    Module.Flat R'
      (CategoryTheory.ModuleCat.Tor.LocalizedTensorSquare.baseChangedModule
        (S := S) (S' := S') (M := M)) := sorry

end

@[stacks 00MO "change-of-rings comparison"]
#check @CategoryTheory.ModuleCat.Tor.QuotientBaseChange.comparison

@[stacks 00MO "flatness conclusion"]
#check @Module.Flat

@[stacks 00MO "localization hypothesis"]
#check @IsLocalization
