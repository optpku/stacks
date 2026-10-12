/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Injective.Baer.Functorial
public import ReasLib.Algebra.Category.ModuleCat.OrdinalSmall
public import ReasLib.CategoryTheory.Abelian.FunctorialInjectives.Definition
public import ReasLib.CategoryTheory.SmallObject.BoundedIteration

@[expose] public section

/-!
# Transfinite Baer Enlargements

The natural one-step Baer inclusion determines a successor structure on endofunctors of
`ModuleCat R`.  Its ordinal-bounded iteration is the specific functor `M ↦ M_α` used in Baer's
argument.  The cardinal bound on ideals supplies ordinal smallness, hence the ideal-extension
criterion and injectivity at a sufficiently large limit stage.
-/

open CategoryTheory
open CategoryTheory.SmallObject
open CategoryTheory.SmallObject.SuccStruct

universe v u

namespace ModuleCat.Baer

variable (R : Type u) [Ring R]

/-- The successor structure on endofunctors induced by the natural one-step Baer inclusion. -/
noncomputable abbrev succStruct :
    SuccStruct (ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R) :=
  SuccStruct.ofNatTrans (inclusionNatTrans R)

/-- The transfinite Baer endofunctor at the ordinal stage `α`. -/
@[stacks 05NX "transfinite Baer functor"]
noncomputable def transfiniteFunctor (α : Ordinal.{max u v}) :
    ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R :=
  SuccStruct.OrdinalBounded.top (succStruct R) α

/-- The transfinite Baer functor is the top object in the ordinal-bounded iteration of the
one-step successor structure. -/
theorem transfiniteFunctor_eq_top (α : Ordinal.{max u v}) :
    transfiniteFunctor R α = SuccStruct.OrdinalBounded.top (succStruct R) α := sorry

/-- The natural map from a module to its transfinite Baer enlargement at stage `α`. -/
@[stacks 05NX "transfinite Baer inclusion"]
noncomputable def transfiniteInclusion (α : Ordinal.{max u v}) :
    𝟭 (ModuleCat.{max u v} R) ⟶ transfiniteFunctor R α :=
  ((succStruct R).ιIterationFunctor (SuccStruct.OrdinalBounded.Shape α)).app
    (SuccStruct.OrdinalBounded.index (le_rfl : α ≤ α))

/-- Each component of the transfinite Baer inclusion is a monomorphism. -/
@[stacks 05NX "monomorphic transfinite inclusion"]
theorem mono_transfiniteInclusion_app (α : Ordinal.{max u v})
    (N : ModuleCat.{max u v} R) :
    Mono ((transfiniteInclusion R α).app N) := sorry

attribute [instance] mono_transfiniteInclusion_app

/-- The transfinite Baer inclusion is a monomorphism in the endofunctor category. -/
@[stacks 05NX "monomorphic transfinite inclusion", instance]
theorem mono_transfiniteInclusion (α : Ordinal.{max u v}) :
    Mono (transfiniteInclusion R α) := sorry

/-- Elementwise form of the monomorphism property of the transfinite Baer inclusion. -/
theorem transfiniteInclusion_app_injective (α : Ordinal.{max u v})
    (N : ModuleCat.{max u v} R) :
    Function.Injective ((transfiniteInclusion R α).app N).hom := sorry

/-- The submodule lattice of an ideal is no larger than the ideal lattice of the ring. -/
theorem idealSubmoduleCardinal_le (I : Ideal R) :
    Cardinal.mk (Submodule R I) ≤ Cardinal.mk (Ideal R) := sorry

/-- The cofinality bound on ideals also bounds the submodule lattice of every ideal. -/
theorem idealSubmoduleCardinal_lt_cof (α : Ordinal.{max u v})
    (hα : Cardinal.lift.{max u v} (Cardinal.mk (Ideal R)) < α.cof) (I : Ideal R) :
    Cardinal.lift.{max u v} (Cardinal.mk (Submodule R I)) < α.cof := sorry

/-- Every ideal module is `α`-small relative to monomorphisms when the lifted cardinality of the
ideal lattice is less than the cofinality of `α`. -/
@[stacks 05NX "ordinal smallness of ideals"]
theorem ideal_isOrdinalSmall (α : Ordinal.{max u v})
    (hα : Cardinal.lift.{max u v} (Cardinal.mk (Ideal R)) < α.cof) (I : Ideal R) :
    (MorphismProperty.monomorphisms (ModuleCat.{max u v} R)).IsOrdinalSmall
      (idealObject R I) α := sorry

/-- Under the cofinality bound, every map from an ideal into a transfinite Baer enlargement
extends across the inclusion of that ideal into `R`. -/
@[stacks 05NX "transfinite ideal extension"]
theorem exists_idealLift (α : Ordinal.{max u v})
    (hα : Cardinal.lift.{max u v} (Cardinal.mk (Ideal R)) < α.cof)
    (N : ModuleCat.{max u v} R) (I : Ideal R)
    (φ : idealObject R I ⟶ (transfiniteFunctor R α).obj N) :
    ∃ φ' : ringObject R ⟶ (transfiniteFunctor R α).obj N,
      (ModuleCat.uliftFunctor.{v, u, u} R).map (ModuleCat.ofHom I.subtype) ≫ φ' = φ := sorry

/-- A universe-lifted transfinite Baer enlargement is injective when the cofinality of its stage
is larger than the lifted cardinality of the ideal lattice. -/
@[stacks 05NX "injective lifted transfinite Baer object"]
theorem liftedTransfiniteFunctor_obj_injective (α : Ordinal.{max u v})
    (hα : Cardinal.lift.{max u v} (Cardinal.mk (Ideal R)) < α.cof)
    (N : ModuleCat.{max u v} R) :
    Injective ((transfiniteFunctor R α).obj N) := sorry

/-- The universe-lifted transfinite Baer functor and its natural inclusion provide functorial
injective embeddings under the lifted cofinality bound. -/
@[stacks 05NX "lifted functorial injective embeddings from Baer iteration", reducible]
noncomputable def liftedFunctorialInjectives (α : Ordinal.{max u v})
    (hα : Cardinal.lift.{max u v} (Cardinal.mk (Ideal R)) < α.cof) :
    HasFunctorialInjectives (ModuleCat.{max u v} R) where
  functor := transfiniteFunctor R α
  ι := transfiniteInclusion R α
  mono_app := mono_transfiniteInclusion_app R α
  injective_obj := liftedTransfiniteFunctor_obj_injective R α hα

/-- A same-universe transfinite Baer enlargement is injective when the
cofinality of its stage is larger than the cardinality of the ideal lattice. -/
@[stacks 05NX "injective transfinite Baer object"]
theorem transfiniteFunctor_obj_injective (α : Ordinal.{u})
    (hα : Cardinal.mk (Ideal R) < α.cof) (N : ModuleCat.{u} R) :
    Injective ((transfiniteFunctor.{0, u} R α).obj N) := sorry

/-- In the same universe, the transfinite Baer functor and its natural
inclusion provide functorial injective embeddings under the unlifted cofinality bound. -/
@[stacks 05NX "functorial injective embeddings from Baer iteration", reducible]
noncomputable def functorialInjectives (α : Ordinal.{u})
    (hα : Cardinal.mk (Ideal R) < α.cof) :
    HasFunctorialInjectives (ModuleCat.{u} R) :=
  liftedFunctorialInjectives.{0, u} R α
    ((Cardinal.lift_id (Cardinal.mk (Ideal R))).symm ▸ hα)

/-- A canonical regular ordinal whose cofinality dominates the ideal lattice of `R`. -/
@[stacks 05NX "canonical Baer ordinal"]
noncomputable def injectiveOrdinal : Ordinal.{max u v} :=
  Cardinal.ord <|
    Order.succ (Cardinal.aleph0 ⊔ Cardinal.lift.{v} (Cardinal.mk (Ideal R)))

/-- The ideal lattice is smaller than the cofinality of `injectiveOrdinal`. -/
theorem idealCardinal_lt_injectiveOrdinal_cof :
    Cardinal.lift.{v} (Cardinal.mk (Ideal R)) < (injectiveOrdinal R).cof := sorry

/-- The canonical Baer iteration supplies functorial injective embeddings in every universe of
`R`-modules containing the ring. -/
@[stacks 05NX "module functorial injective embeddings", reducible]
noncomputable instance (priority := 200) hasFunctorialInjectives :
    HasFunctorialInjectives (ModuleCat.{max u v} R) :=
  liftedFunctorialInjectives R (injectiveOrdinal R)
    (idealCardinal_lt_injectiveOrdinal_cof R)

end ModuleCat.Baer
