module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Proper
public import stacks_project.Chap59.Definition_59_31_3_EtaleSupport
public import stacks_project.Chap59.Lemma_59_79_1_DirectImage

/-!
# Proper-support subfunctor of étale pushforward

For `f : X ⟶ Y` locally of finite type and an abelian sheaf `F` on `X_étale`,
the rule sending `V` in `Y_étale` to the sections of `f_* F` on `V` whose étale
support in `X_V` is proper over `V` is an abelian subpresheaf of `f_* F`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
variable (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})

/-- Evaluating the abelian small-étale pushforward `etaleDirectImage f` on `V`
recovers the sections of `F` on the base change `X_V`. -/
theorem etaleDirectImage_obj_obj (V : Y.Etale) :
    ((etaleDirectImage f).obj F).1.obj (op V) =
      F.1.obj (op ((smallEtalePullback f).obj V)) :=
  sorry

/-- A section of `f_* F` on `V` has proper support over `V` when the closed étale
support of the corresponding section of `F` on `X_V` is proper over `V`. -/
def HasProperSupportOver (V : Y.Etale)
    (σ : ((etaleDirectImage f).obj F).1.obj (op V)) : Prop :=
  ClosedSubset.IsProperOver (pullback.fst V.hom f)
    (abelianSheafSectionSupport F ((smallEtalePullback f).obj V) σ)

/-- Proper support over the base is properness of the étale section support along
`pullback.fst`. -/
theorem hasProperSupportOver_iff (V : Y.Etale)
    (σ : ((etaleDirectImage f).obj F).1.obj (op V)) :
    HasProperSupportOver f F V σ ↔
      ClosedSubset.IsProperOver (pullback.fst V.hom f)
        (abelianSheafSectionSupport F ((smallEtalePullback f).obj V) σ) :=
  sorry

/-- The fiberwise abelian group of sections of `f_* F` on `V` whose étale support
is proper over `V`. -/
def properSupportSections (V : Y.Etale) :
    AddSubgroup (((etaleDirectImage f).obj F).1.obj (op V)) where
  carrier := {σ | HasProperSupportOver f F V σ}
  zero_mem' := sorry
  add_mem' := sorry
  neg_mem' := sorry

/-- Membership in the proper-support sections is the proper-support predicate. -/
theorem mem_properSupportSections_iff (V : Y.Etale)
    (σ : ((etaleDirectImage f).obj F).1.obj (op V)) :
    σ ∈ properSupportSections f F V ↔ HasProperSupportOver f F V σ :=
  sorry

/-- The type-valued subfunctor of `f_* F` whose sections over `V` are those with
étale support proper over `V`. -/
def properSupportSubfunctor :
    Subfunctor (((etaleDirectImage f).obj F).obj ⋙ CategoryTheory.forget AddCommGrpCat) where
  obj W := {σ | HasProperSupportOver f F W.unop σ}
  map := sorry

/-- The value of the proper-support subfunctor on `V` is the set of sections with
proper support over `V`. -/
theorem properSupportSubfunctor_obj (V : Y.Etale) :
    (properSupportSubfunctor f F).obj (op V) =
      {σ | HasProperSupportOver f F V σ} :=
  sorry

/-- Membership in the proper-support subfunctor is membership in the fiberwise
proper-support subgroup. -/
theorem mem_properSupportSubfunctor_obj_iff (V : Y.Etale)
    (σ : ((etaleDirectImage f).obj F).1.obj (op V)) :
    σ ∈ (properSupportSubfunctor f F).obj (op V) ↔
      σ ∈ properSupportSections f F V :=
  sorry

/-- The proper-support subfunctor of `f_* F` is a sheaf on `Y_étale`. Together with
the fiberwise subgroup structure this is an abelian subsheaf of `f_* F`.
Separatedness of `f` is not assumed and is not used to name this subsheaf `f_!`. -/
theorem isSheaf_properSupportSubfunctor :
    Presieve.IsSheaf Y.smallEtaleTopology (properSupportSubfunctor f F).toFunctor :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
