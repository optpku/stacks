/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.GradedModule
public import ReasLib.Algebra.Module.Finite.Explicit
public import ReasLib.Algebra.Module.Graded.Decomposition
public import ReasLib.Algebra.Group.Action.NatInt
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Module.FiniteType
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology.Map
public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.SerreVanishing
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.GradedPullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology of graded module sheaves

This module constructs the total cohomology of a graded module sheaf, its action by a
nonnegatively graded affine algebra, and cohomology of integral twists.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite
open TopologicalSpace
open scoped AlgebraicGeometry DirectSum SheafOfModules.RingedSite.GradedModuleSheaf

noncomputable section

universe u

namespace SheafOfModules.RingedSite.GradedModuleSheaf

/-- The component on an open set of multiplication by a global homogeneous algebra section. -/
@[stacks 0897 "component of the graded cohomology action"]
noncomputable def sectionSmulHomComponent
    {X : Scheme.{u}}
    {pullbackTildeB : GradedAlgebraSheaf.{u, u} X.sheaf}
    (ℱ : GradedModuleSheaf.{u, u} pullbackTildeB)
    (n m : ℤ) (s : (pullbackTildeB.obj m).val.obj (Opposite.op ⊤))
    (U : (Opens X.carrier)ᵒᵖ) :
    (ℱ n).val.obj U ⟶ (ℱ (n + m)).val.obj U :=
  ModuleCat.ofHom ((ℱ.smul n m U).flip
    (((pullbackTildeB.obj m).val.map (homOfLE le_top).op).hom s))

/-- The open-set components of multiplication by a global homogeneous section commute with
restriction. -/
theorem sectionSmulHom_naturality
    {X : Scheme.{u}}
    {pullbackTildeB : GradedAlgebraSheaf.{u, u} X.sheaf}
    (ℱ : GradedModuleSheaf.{u, u} pullbackTildeB)
    (n m : ℤ) (s : (pullbackTildeB.obj m).val.obj (Opposite.op ⊤))
    {U V : (Opens X.carrier)ᵒᵖ} (i : U ⟶ V) :
    (ℱ n).val.map i ≫
        (ModuleCat.restrictScalars ((X.presheaf.map i).hom)).map
          (sectionSmulHomComponent ℱ n m s V) =
      sectionSmulHomComponent ℱ n m s U ≫ (ℱ (n + m)).val.map i := sorry

/-- Multiplication by a global homogeneous algebra section induces a degree-shifting morphism of
a graded module sheaf. -/
@[stacks 0897 "graded section action on cohomology coefficients"]
noncomputable def sectionSmulHom
    {X : Scheme.{u}}
    {pullbackTildeB : GradedAlgebraSheaf.{u, u} X.sheaf}
    (ℱ : GradedModuleSheaf.{u, u} pullbackTildeB)
    (n m : ℤ) (s : (pullbackTildeB.obj m).val.obj (Opposite.op ⊤)) :
    ℱ n ⟶ ℱ (n + m) :=
  ⟨
    { app := fun U ↦ sectionSmulHomComponent ℱ n m s U
      naturality := fun i ↦ sectionSmulHom_naturality ℱ n m s i }
  ⟩

end SheafOfModules.RingedSite.GradedModuleSheaf

namespace AlgebraicGeometry.Scheme.Modules

namespace GradedCohomology

open PullbackTilde

/-- The degree-`n` part of the degree-`p` cohomology of a graded module sheaf. -/
@[stacks 0897 "graded cohomology piece"]
abbrev piece {X : Scheme.{u}}
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    {pullbackTildeB : GradedAlgebraSheaf.{u, u} X.sheaf}
    (ℱ : GradedModuleSheaf.{u, u} pullbackTildeB) (p : ℕ) (n : ℤ) :
    Type u :=
  (RingedSpace.moduleCohomology (ℱ n) p : Type u)

/-- The total degree-`p` cohomology of a graded module sheaf is the direct sum of the cohomology
of its homogeneous pieces. -/
@[stacks 0897 "total graded cohomology"]
abbrev carrier {X : Scheme.{u}}
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    {pullbackTildeB : GradedAlgebraSheaf.{u, u} X.sheaf}
    (ℱ : GradedModuleSheaf.{u, u} pullbackTildeB) (p : ℕ) :
    Type u :=
  DirectSum ℤ fun n ↦ piece ℱ p n

/-- Total graded cohomology unfolds to the direct sum of the cohomology of the homogeneous
pieces. -/
theorem carrier_def {X : Scheme.{u}}
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    {pullbackTildeB : GradedAlgebraSheaf.{u, u} X.sheaf}
    (ℱ : GradedModuleSheaf.{u, u} pullbackTildeB) (p : ℕ) :
    carrier ℱ p =
      DirectSum ℤ fun n ↦ piece ℱ p n := sorry

/-- The explicit homogeneous action on degreewise cohomology, with a scalar of degree `m`
sending the degree-`n` piece to the degree `m +ᵥ n` piece. -/
@[stacks 0897 "degreewise graded cohomology action"]
noncomputable def smul
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    {X : Scheme.{u}} [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Spec (CommRingCat.of A))
    {pullbackTildeB : GradedAlgebraSheaf.{u, u} X.sheaf}
    (pullbackData : Comparison 𝒜 f pullbackTildeB)
    (ℱ : GradedModuleSheaf.{u, u} pullbackTildeB) (p : ℕ)
    {m : ℕ} {n : ℤ} (b : 𝒜 m) (x : piece ℱ p n) :
    piece ℱ p (m +ᵥ n) :=
  ((RingedSpace.moduleCohomologyMap
    (GradedModuleSheaf.sectionSmulHom ℱ n (m : ℤ)
        (pullbackData.homogeneousSection m b) ≫
      eqToHom (congrArg ℱ (Int.add_comm n (m : ℤ)))) p).hom x)

/-- The degree-zero unit acts trivially on degreewise graded cohomology. -/
theorem one_smul
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    {X : Scheme.{u}} [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Spec (CommRingCat.of A))
    {pullbackTildeB : GradedAlgebraSheaf.{u, u} X.sheaf}
    (pullbackData : Comparison 𝒜 f pullbackTildeB)
    (ℱ : GradedModuleSheaf.{u, u} pullbackTildeB) (p : ℕ)
    (x : GradedMonoid (piece ℱ p)) :
    GradedMonoid.mk (0 +ᵥ x.1)
      (smul 𝒜 f pullbackData ℱ p (1 : 𝒜 0) x.2) = x := sorry

/-- Successive homogeneous actions on degreewise cohomology agree with homogeneous
multiplication. -/
theorem mul_smul
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    {X : Scheme.{u}} [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Spec (CommRingCat.of A))
    {pullbackTildeB : GradedAlgebraSheaf.{u, u} X.sheaf}
    (pullbackData : Comparison 𝒜 f pullbackTildeB)
    (ℱ : GradedModuleSheaf.{u, u} pullbackTildeB) (p : ℕ)
    (a b : GradedMonoid (fun d : ℕ ↦ 𝒜 d))
    (x : GradedMonoid (piece ℱ p)) :
    GradedMonoid.mk ((a * b).1 +ᵥ x.1)
        (smul 𝒜 f pullbackData ℱ p (a * b).2 x.2) =
      GradedMonoid.mk (a.1 +ᵥ (b.1 +ᵥ x.1))
        (smul 𝒜 f pullbackData ℱ p a.2
          (smul 𝒜 f pullbackData ℱ p b.2 x.2)) := sorry

/-- A homogeneous scalar distributes over addition in a cohomology piece. -/
theorem smul_add
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    {X : Scheme.{u}} [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Spec (CommRingCat.of A))
    {pullbackTildeB : GradedAlgebraSheaf.{u, u} X.sheaf}
    (pullbackData : Comparison 𝒜 f pullbackTildeB)
    (ℱ : GradedModuleSheaf.{u, u} pullbackTildeB) (p : ℕ)
    {m : ℕ} {n : ℤ} (b : 𝒜 m) (x y : piece ℱ p n) :
    smul 𝒜 f pullbackData ℱ p b (x + y) =
      smul 𝒜 f pullbackData ℱ p b x + smul 𝒜 f pullbackData ℱ p b y := sorry

/-- Every homogeneous scalar sends zero to zero in degreewise cohomology. -/
theorem smul_zero
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    {X : Scheme.{u}} [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Spec (CommRingCat.of A))
    {pullbackTildeB : GradedAlgebraSheaf.{u, u} X.sheaf}
    (pullbackData : Comparison 𝒜 f pullbackTildeB)
    (ℱ : GradedModuleSheaf.{u, u} pullbackTildeB) (p : ℕ)
    {m : ℕ} {n : ℤ} (b : 𝒜 m) :
    smul 𝒜 f pullbackData ℱ p b (0 : piece ℱ p n) = 0 := sorry

/-- Addition of homogeneous scalars distributes through the degreewise cohomology action. -/
theorem add_smul
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    {X : Scheme.{u}} [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Spec (CommRingCat.of A))
    {pullbackTildeB : GradedAlgebraSheaf.{u, u} X.sheaf}
    (pullbackData : Comparison 𝒜 f pullbackTildeB)
    (ℱ : GradedModuleSheaf.{u, u} pullbackTildeB) (p : ℕ)
    {m : ℕ} {n : ℤ} (a b : 𝒜 m) (x : piece ℱ p n) :
    smul 𝒜 f pullbackData ℱ p (a + b) x =
      smul 𝒜 f pullbackData ℱ p a x + smul 𝒜 f pullbackData ℱ p b x := sorry

/-- The zero homogeneous scalar acts by zero on every degreewise cohomology piece. -/
theorem zero_smul
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    {X : Scheme.{u}} [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Spec (CommRingCat.of A))
    {pullbackTildeB : GradedAlgebraSheaf.{u, u} X.sheaf}
    (pullbackData : Comparison 𝒜 f pullbackTildeB)
    (ℱ : GradedModuleSheaf.{u, u} pullbackTildeB) (p : ℕ)
    {m : ℕ} {n : ℤ} (x : piece ℱ p n) :
    smul 𝒜 f pullbackData ℱ p (0 : 𝒜 m) x = 0 := sorry

/-- The graded action on cohomology induced by canonical homogeneous sections of a pullback
affine tilde algebra and multiplication on the graded module sheaf. -/
@[reducible, stacks 0897 "graded action on cohomology"]
noncomputable def gmodule
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    {X : Scheme.{u}} [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Spec (CommRingCat.of A))
    {pullbackTildeB : GradedAlgebraSheaf.{u, u} X.sheaf}
    (pullbackData : Comparison 𝒜 f pullbackTildeB)
    (ℱ : GradedModuleSheaf.{u, u} pullbackTildeB) (p : ℕ) :
    DirectSum.Gmodule (fun d : ℕ ↦ 𝒜 d) (piece ℱ p) where
  smul := smul 𝒜 f pullbackData ℱ p
  one_smul := one_smul 𝒜 f pullbackData ℱ p
  mul_smul := mul_smul 𝒜 f pullbackData ℱ p
  smul_add := smul_add 𝒜 f pullbackData ℱ p
  smul_zero := smul_zero 𝒜 f pullbackData ℱ p
  add_smul := add_smul 𝒜 f pullbackData ℱ p
  zero_smul := zero_smul 𝒜 f pullbackData ℱ p

/-- The module structure on total graded cohomology obtained by restricting the induced graded
action along the homogeneous decomposition of the affine algebra. -/
@[reducible, stacks 0897 "module action on total graded cohomology"]
noncomputable def module
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    {X : Scheme.{u}} [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Spec (CommRingCat.of A))
    {pullbackTildeB : GradedAlgebraSheaf.{u, u} X.sheaf}
    (pullbackData : Comparison 𝒜 f pullbackTildeB)
    (ℱ : GradedModuleSheaf.{u, u} pullbackTildeB) (p : ℕ) :
    Module B (carrier ℱ p) :=
  DirectSum.Gmodule.moduleFor 𝒜 (piece ℱ p) (gmodule 𝒜 f pullbackData ℱ p)

/-- The total degree-`p` cohomology of all homogeneous pieces of a graded module sheaf after an
integral twist by an invertible module. -/
@[stacks 0897 "twisted total graded cohomology"]
abbrev twist {X : Scheme.{u}} [MonoidalCategory X.Modules]
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    {pullbackTildeB : GradedAlgebraSheaf.{u, u} X.sheaf}
    (L : X.Modules) [Invertible L]
    (ℱ : GradedModuleSheaf.{u, u} pullbackTildeB) (d : ℤ) (p : ℕ) : Type u :=
  DirectSum ℤ fun n ↦
    (RingedSpace.moduleCohomology (twistByTensorPower L (ℱ n) d) p : Type u)

/-- Twisted graded cohomology unfolds to the direct sum of cohomology of the twisted homogeneous
pieces. -/
theorem twist_def {X : Scheme.{u}} [MonoidalCategory X.Modules]
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    {pullbackTildeB : GradedAlgebraSheaf.{u, u} X.sheaf}
    (L : X.Modules) [Invertible L]
    (ℱ : GradedModuleSheaf.{u, u} pullbackTildeB) (d : ℤ) (p : ℕ) :
    twist L ℱ d p =
      DirectSum ℤ fun n ↦
        (RingedSpace.moduleCohomology (twistByTensorPower L (ℱ n) d) p : Type u) := sorry

/-- For a proper scheme over a Noetherian affine base, the total cohomology of a quasicoherent
finite-type graded module sheaf is finite over the graded affine algebra under the canonical
pullback-induced action. -/
@[stacks 0897 "finite graded cohomology"]
theorem finite
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] [Algebra.FiniteType A B]
    {X : Scheme.{u}} [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (pullbackTildeB : GradedAlgebraSheaf.{u, u} X.sheaf)
    (pullbackData : Comparison 𝒜 f pullbackTildeB)
    (ℱ : GradedModuleSheaf.{u, u} pullbackTildeB)
    (hℱQuasicoherent : ∀ n : ℤ, (ℱ n).IsQuasicoherent)
    (hℱFiniteType : GradedModuleSheaf.IsFiniteType.{u, u} (𝒜 := pullbackTildeB) ℱ)
    (p : ℕ) :
    Module.FiniteWithAction B (carrier ℱ p) (module 𝒜 f pullbackData ℱ p) := sorry

/-- For a proper scheme over a Noetherian affine base, positive cohomology of every homogeneous
piece of a quasicoherent finite-type graded module sheaf vanishes after one uniformly sufficient
positive ample twist. -/
@[stacks 0897 "eventual vanishing for twisted graded cohomology"]
theorem twist_eventually_isZero
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] [Algebra.FiniteType A B]
    {X : Scheme.{u}} [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (pullbackTildeB : GradedAlgebraSheaf.{u, u} X.sheaf)
    (pullbackData : Comparison 𝒜 f pullbackTildeB)
    (ℱ : GradedModuleSheaf.{u, u} pullbackTildeB)
    (hℱQuasicoherent : ∀ n : ℤ, (ℱ n).IsQuasicoherent)
    (hℱFiniteType : GradedModuleSheaf.IsFiniteType.{u, u} (𝒜 := pullbackTildeB) ℱ)
    [MonoidalCategory X.Modules] (L : X.Modules) [Invertible L] [IsAmple L] :
    ∃ d0 : ℤ, ∀ d : ℤ, d0 ≤ d → ∀ p : ℕ, 0 < p →
      IsZero (AddCommGrpCat.of (twist L ℱ d p)) := sorry

end GradedCohomology

end AlgebraicGeometry.Scheme.Modules
