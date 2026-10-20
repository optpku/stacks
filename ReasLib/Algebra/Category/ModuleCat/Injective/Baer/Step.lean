/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# The One-Step Baer Construction

For an `R`-module `M`, this file forms the coproduct of every map from an ideal of `R` to `M`
and pushes out the coproduct of the ideal inclusions.  Categorical coproducts keep the construction
independent of concrete direct-sum implementations and decidable equality on the index type.
-/

open CategoryTheory Limits

universe v u

namespace ModuleCat.Baer

variable (R : Type u) [Ring R]

/-- An ideal of `R`, regarded canonically as a module in the enlarged carrier universe. -/
abbrev idealObject (I : Ideal R) : ModuleCat.{max u v} R :=
  (ModuleCat.uliftFunctor.{v, u, u} R).obj (ModuleCat.of R I)

/-- The regular module `R`, regarded canonically in the enlarged carrier universe. -/
abbrev ringObject : ModuleCat.{max u v} R :=
  (ModuleCat.uliftFunctor.{v, u, u} R).obj (ModuleCat.of R R)

/-- The indices of the Baer construction on `M`: an ideal together with a morphism into `M`. -/
@[stacks 05NV "Baer indices"]
abbrev Index (M : ModuleCat.{max u v} R) :=
  Σ I : Ideal R, idealObject R I ⟶ M

/-- The family of ideal modules indexed by all ideal maps into `M`. -/
abbrev idealFamily (M : ModuleCat.{max u v} R) (j : Index R M) :
    ModuleCat.{max u v} R :=
  idealObject R j.1

/-- The constant family of copies of `R` indexed by all ideal maps into `M`. -/
abbrev ringFamily (M : ModuleCat.{max u v} R) (_ : Index R M) :
    ModuleCat.{max u v} R :=
  ringObject R

/-- The coproduct of the ideal domains occurring in the Baer span. -/
@[stacks 05NV "coproduct of ideal domains"]
noncomputable abbrev idealCoproduct (M : ModuleCat.{max u v} R) :
    ModuleCat.{max u v} R :=
  ∐ idealFamily R M

/-- The coproduct of copies of `R` occurring in the Baer span. -/
@[stacks 05NV "coproduct of copies of the ring"]
noncomputable abbrev ringCoproduct (M : ModuleCat.{max u v} R) :
    ModuleCat.{max u v} R :=
  ∐ ringFamily R M

/-- The coproduct injection of an ideal domain. -/
noncomputable abbrev idealι (M : ModuleCat.{max u v} R) (j : Index R M) :
    idealObject R j.1 ⟶ idealCoproduct R M :=
  Sigma.ι (idealFamily R M) j

/-- The coproduct injection into the copy of `R` indexed by `j`. -/
noncomputable abbrev ringι (M : ModuleCat.{max u v} R) (j : Index R M) :
    ringObject R ⟶ ringCoproduct R M :=
  Sigma.ι (ringFamily R M) j

/-- The map from the coproduct of ideal domains to `M`, assembled from the indexed maps. -/
@[stacks 05NV "upper span map"]
noncomputable def toModule (M : ModuleCat.{max u v} R) : idealCoproduct R M ⟶ M :=
  Sigma.desc fun j ↦ j.2

/-- The coproduct of the inclusions from each indexed ideal into its corresponding copy of `R`. -/
@[stacks 05NV "left span map"]
noncomputable def toRing (M : ModuleCat.{max u v} R) :
    idealCoproduct R M ⟶ ringCoproduct R M :=
  Sigma.desc fun j ↦
    (ModuleCat.uliftFunctor.{v, u, u} R).map (ModuleCat.ofHom j.1.subtype) ≫ ringι R M j

/-- The `j`th ideal coprojection followed by `toModule` is the map indexed by `j`. -/
@[reassoc (attr := simp)]
theorem idealι_toModule (M : ModuleCat.{max u v} R) (j : Index R M) :
    idealι R M j ≫ toModule R M = j.2 := sorry

/-- The `j`th component of `toRing` is the ideal inclusion into the `j`th copy of `R`. -/
@[reassoc (attr := simp)]
theorem idealι_toRing (M : ModuleCat.{max u v} R) (j : Index R M) :
    idealι R M j ≫ toRing R M =
      (ModuleCat.uliftFunctor.{v, u, u} R).map (ModuleCat.ofHom j.1.subtype) ≫
        ringι R M j := sorry

/-- The object obtained by pushing out the two maps in the Baer span. -/
@[stacks 05NV "Baer step"]
noncomputable def step (M : ModuleCat.{max u v} R) : ModuleCat.{max u v} R :=
  pushout (toRing R M) (toModule R M)

/-- The canonical inclusion of `M` into its one-step Baer enlargement. -/
@[stacks 05NV "canonical inclusion"]
noncomputable abbrev inclusion (M : ModuleCat.{max u v} R) : M ⟶ step R M :=
  pushout.inr (toRing R M) (toModule R M)

/-- The canonical map from the coproduct of copies of `R` into the Baer step. -/
noncomputable abbrev fromRing (M : ModuleCat.{max u v} R) :
    ringCoproduct R M ⟶ step R M :=
  pushout.inl (toRing R M) (toModule R M)

/-- The defining square of the one-step Baer construction commutes. -/
@[stacks 05NV "defining pushout square"]
theorem square (M : ModuleCat.{max u v} R) :
    CommSq (toRing R M) (toModule R M) (fromRing R M) (inclusion R M) := sorry

end ModuleCat.Baer
