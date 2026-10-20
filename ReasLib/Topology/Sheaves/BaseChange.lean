module

public import ReasLib.Topology.Sheaves.Pullback.Composition
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change for sheaves on topological spaces

The direct-image/inverse-image comparison for a commutative square is the right mate of the
canonical square of inverse-image functors.  The coefficient category remains explicit, so this
owner is shared by set-valued, abelian-group-valued, and other concrete sheaf theories.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w v u

namespace TopCat.Sheaf.BaseChange

variable (A : Type u) [Category.{w} A]
variable {FA : A → A → Type v} {CA : A → Type w}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]
variable [HasColimits A] [HasLimits A]
variable [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

/-- The square of inverse-image functors induced by a commutative square of spaces. -/
@[stacks 09V6 "underived sheaf inverse-image square"]
noncomputable def pullbackIso
    {X X' Y Y' : TopCat.{w}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) :
    TopCat.Sheaf.pullback A g ⋙ TopCat.Sheaf.pullback A f' ≅
      TopCat.Sheaf.pullback A f ⋙ TopCat.Sheaf.pullback A g' :=
  TopCat.Sheaf.pullbackComp (A := A) f' g ≪≫
    TopCat.Sheaf.pullbackCongr (A := A) sq.w.symm ≪≫
      (TopCat.Sheaf.pullbackComp (A := A) g' f).symm

/-- The direct-image/inverse-image base-change transformation induced by a commutative square of
spaces. -/
@[stacks 09V6 "underived sheaf base-change transformation"]
noncomputable def map
    {X X' Y Y' : TopCat.{w}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) :
    TopCat.Sheaf.pushforward A f ⋙ TopCat.Sheaf.pullback A g ⟶
      TopCat.Sheaf.pullback A g' ⋙ TopCat.Sheaf.pushforward A f' :=
  (mateEquiv
    (TopCat.Sheaf.pullbackPushforwardAdjunction A f)
    (TopCat.Sheaf.pullbackPushforwardAdjunction A f')
    (pullbackIso A sq).hom).natTrans

end TopCat.Sheaf.BaseChange
