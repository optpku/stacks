module

public import ReasLib.Topology.Sheaf.ExtensionByInitial
public import ReasLib.Topology.Sheaf.Subset.Closed
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Tactic.CrossRefAttribute

/-!
# The canonical sequence for an open subset and its closed complement

For an open subset `U ⊆ X`, this file packages the canonical maps
`j_! j^{-1} F ⟶ F ⟶ i_* i^{-1} F` before evaluating them at an individual sheaf.
The resulting functor to `ShortComplex` makes functoriality in `F` part of the construction,
rather than a separate collection of naturality lemmas.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf.OpenClosed

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/-- The inclusion of the closed complement of an open subset. -/
abbrev complementInclusion (U : Opens X) :
    TopCat.subsetSpace ((U : Set X)ᶜ) ⟶ X :=
  TopCat.subsetInclusion ((U : Set X)ᶜ)

/-- Restriction to `U` followed by extension by zero back to `X`. -/
noncomputable def openPart (U : Opens X) :
    X.Sheaf AddCommGrpCat.{u} ⥤ X.Sheaf AddCommGrpCat.{u} :=
  TopCat.Sheaf.pullback AddCommGrpCat.{u} (TopCat.Opens.Subspace.inclusion U) ⋙
    TopCat.Sheaf.ExtensionByInitial.functor U

/-- Restriction to the closed complement of `U` followed by pushforward to `X`. -/
noncomputable def closedPart (U : Opens X) :
    X.Sheaf AddCommGrpCat.{u} ⥤ X.Sheaf AddCommGrpCat.{u} :=
  TopCat.Sheaf.pullback AddCommGrpCat.{u} (complementInclusion U) ⋙
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} (complementInclusion U)

/-- The counit `j_! j^{-1} ⟶ 𝟭` for the open part. -/
noncomputable def openCounit (U : Opens X) : openPart U ⟶ 𝟭 _ :=
  (TopCat.Sheaf.ExtensionByInitial.Properties.adjunction
    (C := AddCommGrpCat.{u}) U).counit

/-- The unit `𝟭 ⟶ i_* i^{-1}` for the closed part. -/
noncomputable def closedUnit (U : Opens X) : 𝟭 _ ⟶ closedPart U :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
    (complementInclusion U)).unit

/-- The open counit followed by the closed unit is the zero natural transformation. -/
theorem comp_zero (U : Opens X) : openCounit U ≫ closedUnit U = 0 := sorry

/-- The open-closed sequence as a short complex in the endofunctor category. -/
noncomputable def diagram (U : Opens X) :
    ShortComplex (X.Sheaf AddCommGrpCat.{u} ⥤ X.Sheaf AddCommGrpCat.{u}) :=
  ShortComplex.mk (openCounit U) (closedUnit U) (comp_zero U)

/-- Lemma 17.7.1 (02UT) (2): the canonical open-closed short complex is functorial in the
abelian sheaf. -/
@[stacks 02UT "functorial canonical open-closed sequence"]
noncomputable def sequence (U : Opens X) :
    X.Sheaf AddCommGrpCat.{u} ⥤ ShortComplex (X.Sheaf AddCommGrpCat.{u}) :=
  (ShortComplex.functorEquivalence
    (X.Sheaf AddCommGrpCat.{u}) (X.Sheaf AddCommGrpCat.{u})).functor.obj (diagram U)

/-- The first object of the open-closed sequence is the open part. -/
@[simp]
theorem sequence_obj_X₁ (U : Opens X) (F : X.Sheaf AddCommGrpCat.{u}) :
    ((sequence U).obj F).X₁ = (openPart U).obj F := sorry

/-- The middle object of the open-closed sequence is the original sheaf. -/
@[simp]
theorem sequence_obj_X₂ (U : Opens X) (F : X.Sheaf AddCommGrpCat.{u}) :
    ((sequence U).obj F).X₂ = F := sorry

/-- The third object of the open-closed sequence is the closed part. -/
@[simp]
theorem sequence_obj_X₃ (U : Opens X) (F : X.Sheaf AddCommGrpCat.{u}) :
    ((sequence U).obj F).X₃ = (closedPart U).obj F := sorry

/-- The first differential of the open-closed sequence is the open counit. -/
@[simp]
theorem sequence_obj_f (U : Opens X) (F : X.Sheaf AddCommGrpCat.{u}) :
    ((sequence U).obj F).f = (openCounit U).app F := sorry

/-- The second differential of the open-closed sequence is the closed unit. -/
@[simp]
theorem sequence_obj_g (U : Opens X) (F : X.Sheaf AddCommGrpCat.{u}) :
    ((sequence U).obj F).g = (closedUnit U).app F := sorry

/-- On a sheaf morphism, the first component is obtained by applying the open-part functor. -/
@[simp]
theorem sequence_map_τ₁ (U : Opens X) {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G) :
    ((sequence U).map f).τ₁ = (openPart U).map f := sorry

/-- On a sheaf morphism, the middle component is the original morphism. -/
@[simp]
theorem sequence_map_τ₂ (U : Opens X) {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G) :
    ((sequence U).map f).τ₂ = f := sorry

/-- On a sheaf morphism, the third component is obtained by applying the closed-part functor. -/
@[simp]
theorem sequence_map_τ₃ (U : Opens X) {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G) :
    ((sequence U).map f).τ₃ = (closedPart U).map f := sorry

/-- Lemma 17.7.1 (02UT) (1): the canonical open-closed sequence of an abelian sheaf is short
exact. -/
@[stacks 02UT "canonical open-closed sequence is short exact"]
theorem shortExact (U : Opens X) (F : X.Sheaf AddCommGrpCat.{u}) :
    ((sequence U).obj F).ShortExact := sorry

end TopCat.Sheaf.OpenClosed

end

end
