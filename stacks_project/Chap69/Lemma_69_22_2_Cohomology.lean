module

public import Mathlib.Algebra.Module.GradedModule
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.Algebra.Group.Action.NatInt
public import ReasLib.Algebra.Module.Finite.Explicit
public import ReasLib.Algebra.Module.Graded.Decomposition
public import ReasLib.RingTheory.ReesAlgebra.Grading.Decomposition
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap69.Lemma_69_20_4_GradedCohomology
public import stacks_project.Chap69.Lemma_69_22_2_IdealPower

/-!
# Rees cohomology of ideal-power products

The direct sum of the cohomology groups `H^p(X, I^n F)` carries a canonical
graded action of `reesAlgebra I`, obtained by applying affine-base cohomology
to the homogeneous ideal-power action.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

noncomputable section

universe u

variable {A : Type u} [CommRing A]
variable {X : AlgebraicSpace (Spec (CommRingCat.of A))}

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `cohomologyOver`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology

/-- The degree-`n` summand of the cohomology of the product `I^n F`. -/
abbrev piece (I : Ideal A) (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))))
    (F : X.Modules)
    [Abelian X.Modules] [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) : Type u :=
  (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f
    (product I f F n : X.Modules) p : Type u)

/-- The degree-`n` cohomology piece is the underlying type of affine-base cohomology of
`I^n F`. -/
theorem piece_eq (I : Ideal A) (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))))
    (F : X.Modules)
    [Abelian X.Modules] [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) :
    piece I f F p n =
      (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f
        (product I f F n : X.Modules) p : Type u) :=
  sorry

/-- The direct sum of the degree-`p` cohomology groups of `I^n F` over all natural degrees. -/
abbrev carrier (I : Ideal A) (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))))
    (F : X.Modules)
    [Abelian X.Modules] [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ) : Type u :=
  DirectSum ℕ fun n ↦ piece I f F p n

/-- Total ideal-power cohomology unfolds to the direct sum of the cohomology of the products
`I^n F`. -/
theorem carrier_def (I : Ideal A) (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))))
    (F : X.Modules)
    [Abelian X.Modules] [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ) :
    carrier I f F p = DirectSum ℕ fun n ↦ piece I f F p n :=
  sorry

/-- The homogeneous Rees action on ideal-power cohomology. -/
def smul (I : Ideal A) (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))))
    (F : X.Modules)
    [Abelian X.Modules] [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ)
    {m n : ℕ} (a : ReesAlgebra.Grading.grade I m) (x : piece I f F p n) :
    piece I f F p (m +ᵥ n) :=
  (GradedCohomology.cohomologyOverMap (𝟙 (Spec (CommRingCat.of A))) f
      (actionMap I f F (ReesAlgebra.Grading.coefficient I m a)) p).hom x

/-- The degree-zero unit acts trivially on ideal-power cohomology. -/
theorem one_smul (I : Ideal A) (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))))
    (F : X.Modules)
    [Abelian X.Modules] [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ)
    (x : GradedMonoid (piece I f F p)) :
    GradedMonoid.mk (0 +ᵥ x.1)
      (smul I f F p (1 : ReesAlgebra.Grading.grade I 0) x.2) = x :=
  sorry

/-- Successive homogeneous Rees actions agree with homogeneous multiplication. -/
theorem mul_smul (I : Ideal A) (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))))
    (F : X.Modules)
    [Abelian X.Modules] [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ)
    (a b : GradedMonoid (fun d : ℕ ↦ ReesAlgebra.Grading.grade I d))
    (x : GradedMonoid (piece I f F p)) :
    GradedMonoid.mk ((a * b).1 +ᵥ x.1) (smul I f F p (a * b).2 x.2) =
      GradedMonoid.mk (a.1 +ᵥ (b.1 +ᵥ x.1))
        (smul I f F p a.2 (smul I f F p b.2 x.2)) :=
  sorry

/-- A homogeneous Rees scalar distributes over addition in an ideal-power cohomology piece. -/
theorem smul_add (I : Ideal A) (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))))
    (F : X.Modules)
    [Abelian X.Modules] [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ)
    {m n : ℕ} (a : ReesAlgebra.Grading.grade I m) (x y : piece I f F p n) :
    smul I f F p a (x + y) = smul I f F p a x + smul I f F p a y :=
  sorry

/-- Every homogeneous Rees scalar sends zero to zero in ideal-power cohomology. -/
theorem smul_zero (I : Ideal A) (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))))
    (F : X.Modules)
    [Abelian X.Modules] [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ)
    {m n : ℕ} (a : ReesAlgebra.Grading.grade I m) :
    smul I f F p a (0 : piece I f F p n) = 0 :=
  sorry

/-- Addition of homogeneous Rees scalars distributes through the ideal-power cohomology action. -/
theorem add_smul (I : Ideal A) (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))))
    (F : X.Modules)
    [Abelian X.Modules] [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ)
    {m n : ℕ} (a b : ReesAlgebra.Grading.grade I m) (x : piece I f F p n) :
    smul I f F p (a + b) x = smul I f F p a x + smul I f F p b x :=
  sorry

/-- The zero homogeneous Rees scalar acts by zero on ideal-power cohomology. -/
theorem zero_smul (I : Ideal A) (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))))
    (F : X.Modules)
    [Abelian X.Modules] [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ)
    {m n : ℕ} (x : piece I f F p n) :
    smul I f F p (0 : ReesAlgebra.Grading.grade I m) x = 0 :=
  sorry

/-- The explicit graded Rees action on ideal-power cohomology. -/
@[reducible]
def gmodule (I : Ideal A) (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))))
    (F : X.Modules)
    [Abelian X.Modules] [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ) :
    DirectSum.Gmodule (fun n ↦ ReesAlgebra.Grading.grade I n) (piece I f F p) where
  smul := smul I f F p
  one_smul := one_smul I f F p
  mul_smul := mul_smul I f F p
  smul_add := smul_add I f F p
  smul_zero := smul_zero I f F p
  add_smul := add_smul I f F p
  zero_smul := zero_smul I f F p

/-- The canonical Rees algebra module structure on total ideal-power cohomology. -/
@[reducible]
def module (I : Ideal A) (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))))
    (F : X.Modules)
    [Abelian X.Modules] [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ) :
    Module (reesAlgebra I) (carrier I f F p) :=
  DirectSum.Gmodule.moduleFor (ReesAlgebra.Grading.grade I) (piece I f F p)
    (gmodule I f F p)

/-- Under `module`, a homogeneous scalar acts on a pure cohomology summand through `smul`. -/
theorem module_smul_of (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))))
    (F : X.Modules)
    [Abelian X.Modules] [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ)
    {m n : ℕ} (a : ReesAlgebra.Grading.grade I m) (x : piece I f F p n) :
    (module I f F p).toSMul.smul a (DirectSum.of (piece I f F p) n x) =
      DirectSum.of (piece I f F p) (m +ᵥ n) (smul I f F p a x) :=
  sorry

/-- In Situation 69.22.1, the graded `reesAlgebra I`-module `⨁ n, H^p(X, I^n F)` is finite. -/
theorem finite [IsNoetherianRing A] (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) [Proper f]
    (F : X.Modules) [F.IsCoherent]
    [Abelian X.Modules] [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ) :
    Module.FiniteWithAction (reesAlgebra I) (carrier I f F p) (module I f F p) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology
