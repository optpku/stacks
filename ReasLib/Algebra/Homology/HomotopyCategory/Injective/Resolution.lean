module

public import ReasLib.Algebra.Homology.HomotopyCategory.Injective
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Functorial Bounded-Below Injective Resolutions

This leaf owns noncanonical choices of bounded-below injective resolutions and
their functorial realization in the bounded-below homotopy category. The
termwise-injective homotopy subcategory itself remains in `Injective.lean`.
-/

open CategoryTheory
open CategoryTheory.ObjectProperty

universe v u

namespace CategoryTheory.HomotopyCategory.Plus

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]

/-- A functorial bounded-below injective resolution. Its
comparison maps are quasi-isomorphisms in the bounded-below homotopy category.
-/
@[stacks 013W]
structure InjectiveResolutionFunctor where
  /-- The resolution functor into bounded-below injective homotopy objects. -/
  toFunctor : HomotopyCategory.Plus 𝒜 ⥤ Injective 𝒜
  /-- The natural quasi-isomorphism from a complex to its resolution. -/
  ι : 𝟭 (HomotopyCategory.Plus 𝒜) ⟶ toFunctor ⋙ Injective.ι 𝒜
  /-- Every component of the comparison morphism is a quasi-isomorphism. -/
  quasiIso_app (K : HomotopyCategory.Plus 𝒜) :
    HomotopyCategory.Plus.quasiIso 𝒜 (ι.app K)

namespace InjectiveResolutionFunctor

variable {𝒜}

/-- A functor into bounded-below injective homotopy objects and a natural comparison
with quasi-isomorphism components define a functorial injective resolution. -/
def ofComparison (F : HomotopyCategory.Plus 𝒜 ⥤ Injective 𝒜)
    (comparison : 𝟭 (HomotopyCategory.Plus 𝒜) ⟶ F ⋙ Injective.ι 𝒜)
    (h_quasiIso : ∀ K, HomotopyCategory.Plus.quasiIso 𝒜 (comparison.app K)) :
    InjectiveResolutionFunctor 𝒜 :=
  { toFunctor := F, ι := comparison, quasiIso_app := h_quasiIso }

/-- The resolution constructed from a comparison has the supplied functor and natural
comparison, and each of its comparison components is a quasi-isomorphism. -/
theorem ofComparison_spec (F : HomotopyCategory.Plus 𝒜 ⥤ Injective 𝒜)
    (comparison : 𝟭 (HomotopyCategory.Plus 𝒜) ⟶ F ⋙ Injective.ι 𝒜)
    (h_quasiIso : ∀ K, HomotopyCategory.Plus.quasiIso 𝒜 (comparison.app K)) :
    (ofComparison F comparison h_quasiIso).toFunctor = F ∧
      (ofComparison F comparison h_quasiIso).ι = comparison ∧
      ∀ K, HomotopyCategory.Plus.quasiIso 𝒜
        ((ofComparison F comparison h_quasiIso).ι.app K) := sorry

end InjectiveResolutionFunctor

end CategoryTheory.HomotopyCategory.Plus

namespace CochainComplex

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]

/-- A choice of a bounded-below injective resolution for every
bounded-below cochain complex. This is deliberately data, not a functor:
functoriality is supplied separately by `InjectiveResolutionFunctor`. -/
@[stacks 013W]
abbrev InjectiveResolutionChoice :=
  (K : CochainComplex.Plus 𝒜) → InjectiveResolution K.obj

namespace InjectiveResolutionChoice

/-- The homotopy image of a selected bounded-below injective resolution has
injective terms. -/
theorem homotopyObj_mem (R : InjectiveResolutionChoice 𝒜)
    (K : CochainComplex.Plus 𝒜) :
    HomotopyCategory.Plus.injective 𝒜
      ((HomotopyCategory.Plus.quotient 𝒜).obj
        (R K : CochainComplex.Plus 𝒜)) := sorry

/-- The chosen resolution of `K`, regarded as an object of `K⁺ᵢ(𝒜)`. -/
noncomputable def homotopyObj (R : InjectiveResolutionChoice 𝒜)
    (K : CochainComplex.Plus 𝒜) : HomotopyCategory.Plus.Injective 𝒜 :=
  ⟨(HomotopyCategory.Plus.quotient 𝒜).obj (R K : CochainComplex.Plus 𝒜),
    homotopyObj_mem 𝒜 R K⟩

/-- The chosen comparison morphism `K ⟶ R(K)` in the bounded-below homotopy
category. -/
noncomputable def comparison (R : InjectiveResolutionChoice 𝒜)
    (K : CochainComplex.Plus 𝒜) :
    (HomotopyCategory.Plus.quotient 𝒜).obj K ⟶
      (HomotopyCategory.Plus.Injective.ι 𝒜).obj (homotopyObj 𝒜 R K) :=
  (HomotopyCategory.Plus.quotient 𝒜).map ⟨(R K).ι⟩

/-- A functorial injective resolution realizes an objectwise resolution choice
when its values and comparison maps agree with that choice up to unique
compatible isomorphism. -/
def IsRealizedBy (R : InjectiveResolutionChoice 𝒜)
    (J : HomotopyCategory.Plus.InjectiveResolutionFunctor 𝒜) : Prop :=
  ∀ K : CochainComplex.Plus 𝒜,
    ∃! eK : J.toFunctor.obj ((HomotopyCategory.Plus.quotient 𝒜).obj K) ≅
        homotopyObj 𝒜 R K,
      J.ι.app ((HomotopyCategory.Plus.quotient 𝒜).obj K) ≫
          (HomotopyCategory.Plus.Injective.ι 𝒜).map eK.hom = comparison 𝒜 R K

/-- Every objectwise choice of bounded-below injective
resolutions admits a functorial realization in the homotopy category. -/
@[stacks 05TJ]
theorem exists_resolutionFunctor (R : InjectiveResolutionChoice 𝒜) :
    ∃ J : HomotopyCategory.Plus.InjectiveResolutionFunctor 𝒜,
      IsRealizedBy 𝒜 R J := sorry

end InjectiveResolutionChoice

/-- Enough injectives provide an objectwise choice of
bounded-below injective resolutions. -/
@[stacks 013X]
theorem nonempty_injectiveResolutionChoice [EnoughInjectives 𝒜] :
    Nonempty (InjectiveResolutionChoice 𝒜) := sorry

end CochainComplex

namespace CategoryTheory.HomotopyCategory.Plus.Injective

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- Every bounded-below homotopy object admits a quasi-isomorphism
to a bounded-below homotopy object with injective terms. -/
@[stacks 05TI]
theorem exists_quasiIso [EnoughInjectives 𝒜]
    (X : HomotopyCategory.Plus 𝒜) :
    ∃ (I : HomotopyCategory.Plus.Injective 𝒜)
      (s : X ⟶ (HomotopyCategory.Plus.Injective.ι 𝒜).obj I),
      HomotopyCategory.Plus.quasiIso 𝒜 s := sorry

end CategoryTheory.HomotopyCategory.Plus.Injective

namespace CategoryTheory.HomotopyCategory.Plus.InjectiveResolutionFunctor

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- Enough injectives provide a functorial bounded-below
injective resolution. -/
@[stacks 013X]
theorem nonempty [EnoughInjectives 𝒜] :
    Nonempty (HomotopyCategory.Plus.InjectiveResolutionFunctor 𝒜) := sorry

/-- Two functorial bounded-below injective resolutions have a
unique natural isomorphism compatible with their comparison maps. -/
@[stacks 013X]
theorem existsUniqueIso (J J' : HomotopyCategory.Plus.InjectiveResolutionFunctor 𝒜) :
    ∃! e : J.toFunctor ≅ J'.toFunctor,
      J.ι ≫ Functor.whiskerRight e.hom (HomotopyCategory.Plus.Injective.ι 𝒜) = J'.ι := sorry

end CategoryTheory.HomotopyCategory.Plus.InjectiveResolutionFunctor
