module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.Pullback
public import stacks_project.Chap85.Lemma_85_16_1_Localization

/-!
# Lower shriek along total localization of a simplicial semi-representable object

The functors `a^{Sh}_!` and `a_!` are sheaf pullback along the continuous localization
`totalForget`, left adjoint to continuous sheaf pushforward (Sites, Lemma 7.21.5 and
Modules on Sites, Lemma 18.16.2).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (K : SimplicialObject (FormalCoproduct.{w} C))
variable [HasWeakSheafify J (Type (max w u v))]
variable [HasWeakSheafify J AddCommGrpCat.{max w u v}]
variable [∀ P : (Grothendieck (overSiteDiagram K))ᵒᵖ ⥤ Type (max w u v),
  (totalForget K).op.HasLeftKanExtension P]
variable [∀ P : (Grothendieck (overSiteDiagram K))ᵒᵖ ⥤ AddCommGrpCat.{max w u v},
  (totalForget K).op.HasLeftKanExtension P]

/-- The functor `a^{Sh}_! : Sh((C / K)_total) ⥤ Sh(C)`, sheaf pullback along `j_total`. -/
abbrev sheafLowerShriek :
    Sheaf (overSiteTotalTopology J K) (Type (max w u v)) ⥤
      Sheaf J (Type (max w u v)) :=
  (totalForget K).sheafPullback (Type (max w u v)) (overSiteTotalTopology J K) J

/-- The functor `a_! : Ab((C / K)_total) ⥤ Ab(C)`, sheaf pullback along `j_total`. -/
abbrev abelianLowerShriek :
    Sheaf (overSiteTotalTopology J K) AddCommGrpCat.{max w u v} ⥤
      Sheaf J AddCommGrpCat.{max w u v} :=
  (totalForget K).sheafPullback AddCommGrpCat.{max w u v} (overSiteTotalTopology J K) J

/-- `a^{Sh}_!` is left adjoint to continuous sheaf pushforward of `j_total`. -/
instance sheafLowerShriek_isLeftAdjoint : (sheafLowerShriek J K).IsLeftAdjoint :=
  ((totalForget K).sheafAdjunctionContinuous (Type (max w u v))
    (overSiteTotalTopology J K) J).isLeftAdjoint

/-- `a_!` is left adjoint to continuous sheaf pushforward of `j_total` on abelian sheaves. -/
instance abelianLowerShriek_isLeftAdjoint : (abelianLowerShriek J K).IsLeftAdjoint :=
  ((totalForget K).sheafAdjunctionContinuous AddCommGrpCat.{max w u v}
    (overSiteTotalTopology J K) J).isLeftAdjoint

end CategoryTheory.SemiRepresentableFamily
