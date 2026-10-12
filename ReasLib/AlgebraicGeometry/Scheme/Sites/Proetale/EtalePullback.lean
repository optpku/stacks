/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Comparison from the small étale site to the small pro-étale site

The comparison functor `ε : S.Etale ⥤ S.ProEt` is the change-of-property functor
along `Etale ≤ WeaklyEtale`, and `ε⁻¹` is the associated sheaf pullback.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

/-- The comparison functor `ε : S_étale ⥤ S_proétale` induced by
`Etale ≤ WeaklyEtale`. -/
def etaleToProEt (S : Scheme.{u}) : S.Etale ⥤ S.ProEt :=
  MorphismProperty.Over.changeProp S etale_le_weaklyEtale le_rfl

/-- `etaleToProEt` does not change the underlying scheme of an object. -/
theorem etaleToProEt_obj_left (S : Scheme.{u}) (U : S.Etale) :
    ((etaleToProEt S).obj U).left = U.left := sorry

/-- `etaleToProEt` does not change the structure morphism of an object. -/
theorem etaleToProEt_obj_hom (S : Scheme.{u}) (U : S.Etale) :
    ((etaleToProEt S).obj U).hom = U.hom := sorry

/-- The comparison functor `ε` is continuous for the small étale and small
pro-étale topologies. -/
instance etaleToProEt_isContinuous (S : Scheme.{u}) :
    (etaleToProEt S).IsContinuous S.smallEtaleTopology (topology S) := sorry

/-- Restriction (sheaf pushforward) along `etaleToProEt` is a right adjoint and
therefore admits the inverse-image left adjoint `ε⁻¹`. -/
instance etaleToProEt_sheafPushforward_isRightAdjoint (S : Scheme.{u}) :
    ((etaleToProEt S).sheafPushforwardContinuous AddCommGrpCat.{u}
      S.smallEtaleTopology (topology S)).IsRightAdjoint := sorry

/-- Inverse image `ε⁻¹` of abelian sheaves along the comparison morphism from
the small étale site to the small pro-étale site. -/
abbrev etaleSheafPullback (S : Scheme.{u}) :
    Sheaf S.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf (topology S) AddCommGrpCat.{u} :=
  (etaleToProEt S).sheafPullback AddCommGrpCat.{u} S.smallEtaleTopology (topology S)

/-- `etaleSheafPullback` is sheaf pullback along `etaleToProEt`. -/
theorem etaleSheafPullback_def (S : Scheme.{u}) :
    etaleSheafPullback S =
      (etaleToProEt S).sheafPullback AddCommGrpCat.{u}
        S.smallEtaleTopology (topology S) := sorry

end AlgebraicGeometry.Scheme.ProEt
