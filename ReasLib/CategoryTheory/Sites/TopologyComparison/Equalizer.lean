/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.TopologyComparison.Situation
public import ReasLib.CategoryTheory.Sites.Cohomology.Objectwise
public import ReasLib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Equalizer descent for topology-comparison cohomology

The base-change object below packages the pullback along a morphism in the comparison situation.
This keeps the source-facing equalizer statement independent of a global pullback instance on the
ambient category.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u v

namespace CategoryTheory.GrothendieckTopology.TopologyComparison

variable {C : Type u} [Category.{v} C]
variable {τ τ' : GrothendieckTopology C}
variable {P : MorphismProperty C}
variable {A' : ∀ X : C,
  ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v})}

namespace Situation

/-- The pullback square in Over Y attached to f ∈ P and an object U → Y. -/
@[stacks 0EZD "situation base-change square"]
structure BaseChange
    (h : Situation τ τ' P A') {X Y : C} (f : X ⟶ Y) (hf : P f) (U : Over Y) where
  /-- The pullback object, regarded as an object over Y. -/
  obj : Over Y
  /-- The projection to f : X ⟶ Y. -/
  fst : obj ⟶ Over.mk f
  /-- The projection to U → Y. -/
  snd : obj ⟶ U
  /-- The underlying square is a pullback. -/
  isPullback : IsPullback fst.left snd.left f U.hom

namespace BaseChange

/-- The canonical base-change square obtained from the pullback axiom in Situation. -/
@[stacks 0EZD "canonical situation base-change square"]
noncomputable def canonical
    (h : Situation τ τ' P A') {X Y : C} (f : X ⟶ Y) (hf : P f) (U : Over Y) :
    BaseChange h f hf U :=
  -- The situation stores pullback existence as a field; these local certificates select the
  -- canonical pullback object without polluting global instance search.
  letI : P.HasPullbacks := h.hasPullbacks
  letI : HasPullback f U.hom :=
    MorphismProperty.HasPullbacks.hasPullback (P := P) U.hom hf
  { obj := Over.mk (pullback.fst f U.hom ≫ f)
    fst := Over.homMk (pullback.fst f U.hom)
    snd := Over.homMk (pullback.snd f U.hom) (pullback.condition.symm)
    isPullback := IsPullback.of_hasPullback f U.hom }

end BaseChange

end Situation

namespace Cohomology

variable [∀ X : C, HasSheafify (τ'.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C,
  HasInjectiveResolutions (Sheaf (τ'.over X) AddCommGrpCat.{max u v})]
variable [∀ {X Y : C} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
      (τ'.over X) (τ'.over Y))]
variable [∀ X : C,
  HasExt.{max u v} (Sheaf (τ'.over X) AddCommGrpCat.{max u v})]

/-- Lemma 21.30.6 (0EZD): an equalizer class on a P-cover becomes zero after a
τ'-cover of the base. -/
@[stacks 0EZD]
theorem equalizerVanishes
    (h : Situation τ τ' P A')
    {X Y : C} (f : X ⟶ Y) (hf : P f)
    (hcover : (τ.over Y).CoversTop (fun _ : PUnit ↦ Over.mk f))
    (F' : Sheaf (τ'.over Y) AddCommGrpCat.{max u v}) (hF' : A' Y F')
    (n : ℕ)
    (θ : Sheaf.cohomologyOverObject F' (Over.mk f) (n + 1))
    (hθ :
      (Sheaf.uliftCohomologyPresheaf (τ'.over Y) F' (n + 1)).map
          (Situation.BaseChange.canonical h f hf (Over.mk f)).fst.op θ =
        (Sheaf.uliftCohomologyPresheaf (τ'.over Y) F' (n + 1)).map
          (Situation.BaseChange.canonical h f hf (Over.mk f)).snd.op θ) :
    ∃ T : (τ'.over Y).Cover (Over.mk (𝟙 Y)), ∀ I : T.Arrow,
      (Sheaf.uliftCohomologyPresheaf (τ'.over Y) F' (n + 1)).map
          (Situation.BaseChange.canonical h f hf I.Y).fst.op θ = 0 := sorry

end Cohomology

end CategoryTheory.GrothendieckTopology.TopologyComparison

end
