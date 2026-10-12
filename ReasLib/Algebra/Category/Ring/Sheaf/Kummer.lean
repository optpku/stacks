/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.Ring.Sheaf.Units
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Limits

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The sheaf-level additive `n`-fold map on the units sheaf. -/
noncomputable def unitsNsmul
    (𝒪 : Sheaf J CommRingCat.{max u v}) (n : ℕ) :
    unitsAddSheaf 𝒪 ⟶ unitsAddSheaf 𝒪 :=
  n • 𝟙 (unitsAddSheaf 𝒪)

/-- The kernel sheaf of the additive `n`-fold map, modeling roots of unity. -/
noncomputable abbrev rootsOfUnityAddSheaf
    (𝒪 : Sheaf J CommRingCat.{max u v}) (n : ℕ) :
    Sheaf J AddCommGrpCat.{max u v} :=
  kernel (unitsNsmul 𝒪 n)

/-- The short complex consisting of the roots-of-unity kernel and the additive `n`-fold map. -/
noncomputable def kummerAddShortComplex
    (𝒪 : Sheaf J CommRingCat.{max u v}) (n : ℕ) :
    ShortComplex (Sheaf J AddCommGrpCat.{max u v}) :=
  ShortComplex.mk (kernel.ι (unitsNsmul 𝒪 n)) (unitsNsmul 𝒪 n)
    (kernel.condition (unitsNsmul 𝒪 n))

/-- The component of `unitsNsmul` is the ordinary additive `n`-fold homomorphism on units. -/
theorem unitsNsmul_app
    (𝒪 : Sheaf J CommRingCat.{max u v}) (n : ℕ) (U : Cᵒᵖ) :
    (unitsNsmul 𝒪 n).hom.app U = AddCommGrpCat.ofHom (nsmulAddMonoidHom n) := sorry

/-- The additive roots-of-unity sheaf is the kernel of the additive `n`-fold map. -/
theorem rootsOfUnityAddSheaf_eq_kernel
    (𝒪 : Sheaf J CommRingCat.{max u v}) (n : ℕ) :
    rootsOfUnityAddSheaf 𝒪 n = kernel (unitsNsmul 𝒪 n) := sorry

/-- The first map of `kummerAddShortComplex` is the kernel inclusion. -/
theorem kummerAddShortComplex_f
    (𝒪 : Sheaf J CommRingCat.{max u v}) (n : ℕ) :
    (kummerAddShortComplex 𝒪 n).f = kernel.ι (unitsNsmul 𝒪 n) := sorry

/-- The second map of `kummerAddShortComplex` is the additive sheaf-level `n`-fold map. -/
theorem kummerAddShortComplex_g
    (𝒪 : Sheaf J CommRingCat.{max u v}) (n : ℕ) :
    (kummerAddShortComplex 𝒪 n).g = unitsNsmul 𝒪 n := sorry

end CategoryTheory.Sheaf

end
