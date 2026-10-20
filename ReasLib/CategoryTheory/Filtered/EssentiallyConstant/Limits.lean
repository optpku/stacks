module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Diagram

/-!
# Universal properties of essentially constant presentations

An essentially constant cocone is already a colimit cocone, and an essentially constant cone is
already a limit cone.  The mediating maps are explicit projections of the stored split leg; only
their universal-property laws are deferred.

The chosen presentation witnesses are encapsulated by named `desc`/`lift`, factorization, and
uniqueness APIs, so applications do not inspect existential choices.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe uI vI uC vC

namespace CategoryTheory

variable {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]

/-
The canonical conclusions are `IsColimit c` and `IsLimit c`, not a new project-level notion of
"the value" of an essentially constant system. The presentation-level certificates determine the
mediating maps explicitly, even without `[IsFiltered I]` or `[IsCofiltered I]`.

Extracting the distinguished stage and splitting from an existential proof is necessarily
noncomputable.  The choice is encapsulated in `desc` and `lift`; their `fac` and `uniq` theorems
give the public specification and show that downstream users never need to inspect
`Exists.choose`. Only those proposition-valued universal-property laws are deferred. The
diagram-level namespaces retain the filtered/cofiltered orientation, but packaging the same
chosen presentation as a canonical `ColimitCocone` or `LimitCone` needs neither class assumption.

Mathlib's `Functor.IsEventuallyConstantFrom.hasColimit` and
`Functor.IsEventuallyConstantTo.hasLimit` remain useful stronger special cases, but cannot replace
the split-leg and eventual-factorization hypothesis.  The invariant `Ind`/`Pro` reformulations
belong to the Ind/Pro layer rather than this universal-property construction.
-/

namespace Limits.Cocone.IsEssentiallyConstant

/-- The descent morphism from an essentially constant cocone to any competing cocone. -/
@[stacks 05PU "descent from an essentially constant cocone"]
noncomputable def desc {M : I ⥤ C} {c : Cocone M}
    (hc : c.IsEssentiallyConstant) (s : Cocone M) : c.pt ⟶ s.pt :=
  hc.stageSplitEpi.section_ ≫ s.ι.app hc.stage

/-- The canonical descent morphism commutes with every cocone leg. -/
theorem desc_fac {M : I ⥤ C} {c : Cocone M}
    (hc : c.IsEssentiallyConstant) (s : Cocone M) (j : I) :
    c.ι.app j ≫ hc.desc s = s.ι.app j := sorry
/- Proof strategy: take `k`, `ik`, and `jk` from the factorization clause at `j`; rewrite
`s.ι.app hc.stage` by cocone naturality along `ik`, substitute the stored factorization, and
finish with cocone naturality along `jk`. -/

/-- The canonical descent morphism is uniquely determined by its composites with the cocone
legs. -/
theorem desc_uniq {M : I ⥤ C} {c : Cocone M}
    (hc : c.IsEssentiallyConstant) (s : Cocone M) (m : c.pt ⟶ s.pt)
    (hm : ∀ j : I, c.ι.app j ≫ m = s.ι.app j) : m = hc.desc s := sorry
/- Proof strategy: insert `σ.section_ ≫ c.ι.app i = 𝟙 c.pt` at the chosen stage `i`, then apply
`hm i` and unfold `desc`.  This proof also shows independence from the existentially chosen
presentation witness. -/

/-- The explicit colimit universal property carried by an essentially constant cocone. -/
@[stacks 05PU "colimit property of an essentially constant cocone"]
noncomputable def isColimit {M : I ⥤ C} {c : Cocone M}
    (hc : c.IsEssentiallyConstant) : IsColimit c where
  desc := hc.desc
  fac := desc_fac hc
  uniq := desc_uniq hc

end Limits.Cocone.IsEssentiallyConstant

namespace Limits.Cone.IsEssentiallyConstant

/-- The lift morphism from any competing cone to an essentially constant cone. -/
@[stacks 05PU "lift to an essentially constant cone"]
noncomputable def lift {M : I ⥤ C} {c : Cone M}
    (hc : c.IsEssentiallyConstant) (s : Cone M) : s.pt ⟶ c.pt :=
  s.π.app hc.stage ≫ hc.stageSplitMono.retraction

/-- The canonical lift morphism commutes with every cone leg. -/
theorem lift_fac {M : I ⥤ C} {c : Cone M}
    (hc : c.IsEssentiallyConstant) (s : Cone M) (j : I) :
    hc.lift s ≫ c.π.app j = s.π.app j := sorry
/- Proof strategy: take the common predecessor `k` and maps `ki`, `kj` from the factorization
clause; rewrite `s.π.app hc.stage` by cone naturality along `ki`, substitute the stored
factorization, and finish with cone naturality along `kj`. -/

/-- The canonical lift morphism is uniquely determined by its composites with the cone legs. -/
theorem lift_uniq {M : I ⥤ C} {c : Cone M}
    (hc : c.IsEssentiallyConstant) (s : Cone M) (m : s.pt ⟶ c.pt)
    (hm : ∀ j : I, m ≫ c.π.app j = s.π.app j) : m = hc.lift s := sorry
/- Proof strategy: insert `c.π.app i ≫ σ.retraction = 𝟙 c.pt` at the chosen stage `i`, apply
`hm i`, and unfold `lift`.  Uniqueness makes the result independent of the chosen presentation
witness. -/

/-- The explicit limit universal property carried by an essentially constant cone. -/
@[stacks 05PU "limit property of an essentially constant cone"]
noncomputable def isLimit {M : I ⥤ C} {c : Cone M}
    (hc : c.IsEssentiallyConstant) : IsLimit c where
  lift := hc.lift
  fac := lift_fac hc
  uniq := lift_uniq hc

end Limits.Cone.IsEssentiallyConstant

namespace IsFiltered.IsEssentiallyConstant

/-- The canonical selected colimit cocone carried by an essentially constant filtered-oriented
presentation. Its cocone is selected directly from `hM`; its universal property is the explicit
one supplied by `Limits.Cocone.IsEssentiallyConstant.isColimit`. -/
@[stacks 05PV "selected colimit of an essentially constant filtered diagram"]
noncomputable def colimitCocone {M : I ⥤ C}
    (hM : IsFiltered.IsEssentiallyConstant M) :
    ColimitCocone M where
  cocone := hM.cocone
  isColimit := hM.choose_spec.isColimit

/-- The selected colimit cocone retains the essential-constancy presentation from which it was
constructed. -/
theorem colimitCocone.isEssentiallyConstant {M : I ⥤ C}
    (hM : IsFiltered.IsEssentiallyConstant M) :
    hM.colimitCocone.cocone.IsEssentiallyConstant := sorry

/-- An essentially constant filtered-oriented presentation supplies the canonical `HasColimit`
property for its diagram. This bridge lets applications install the selected universal property
as a local instance without unpacking a cocone existential. -/
theorem hasColimit {M : I ⥤ C}
    (hM : IsFiltered.IsEssentiallyConstant M) :
    HasColimit M := sorry

/-- An essentially constant filtered-oriented diagram admits a colimit cocone whose underlying
cocone exhibits the same essential-constancy presentation. -/
theorem exists_colimitCocone {M : I ⥤ C}
    (hM : IsFiltered.IsEssentiallyConstant M) :
    ∃ c : ColimitCocone M, c.cocone.IsEssentiallyConstant := sorry
/- Proof strategy: unpack `hM` as `⟨c, hc⟩`, form the explicit colimit cocone
`⟨c, hc.isColimit⟩`, and retain `hc` for its unchanged underlying cocone. -/

end IsFiltered.IsEssentiallyConstant

namespace IsCofiltered.IsEssentiallyConstant

/-- The canonical selected limit cone carried by an essentially constant cofiltered-oriented
presentation. Its cone is selected directly from `hM`; its universal property is the explicit one
supplied by `Limits.Cone.IsEssentiallyConstant.isLimit`. -/
@[stacks 05PV "selected limit of an essentially constant cofiltered diagram"]
noncomputable def limitCone {M : I ⥤ C}
    (hM : IsCofiltered.IsEssentiallyConstant M) :
    LimitCone M where
  cone := hM.cone
  isLimit := hM.choose_spec.isLimit

/-- The selected limit cone retains the essential-constancy presentation from which it was
constructed. -/
theorem limitCone.isEssentiallyConstant {M : I ⥤ C}
    (hM : IsCofiltered.IsEssentiallyConstant M) :
    hM.limitCone.cone.IsEssentiallyConstant := sorry

/-- An essentially constant cofiltered-oriented presentation supplies the canonical `HasLimit`
property for its diagram. This bridge lets applications install the selected universal property
as a local instance without unpacking a cone existential. -/
theorem hasLimit {M : I ⥤ C}
    (hM : IsCofiltered.IsEssentiallyConstant M) :
    HasLimit M := sorry

/-- An essentially constant cofiltered-oriented diagram admits a limit cone whose underlying cone
exhibits the same essential-constancy presentation. -/
theorem exists_limitCone {M : I ⥤ C}
    (hM : IsCofiltered.IsEssentiallyConstant M) :
    ∃ c : LimitCone M, c.cone.IsEssentiallyConstant := sorry
/- Proof strategy: unpack `hM` as `⟨c, hc⟩`, form the explicit limit cone `⟨c, hc.isLimit⟩`, and
retain `hc` for its unchanged underlying cone. -/

end IsCofiltered.IsEssentiallyConstant

end CategoryTheory


