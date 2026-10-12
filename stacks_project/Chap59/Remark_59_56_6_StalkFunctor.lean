/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_29_7
public import stacks_project.Chap59.Lemma_59_36_2_Stalk

open CategoryTheory
open AlgebraicGeometry

@[expose] public section

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Etale

variable {S : Scheme.{u}} (s : GeometricPoint S)

/-- The functor of étale stalks at a geometric point `s̄`. -/
def stalkFunctor : Sheaf S.smallEtaleTopology (Type u) ⥤ Type u :=
  (GeometricPoint.toSmallEtalePoint s).sheafFiber

/-- The stalk functor evaluates to the site-point sheaf fibre. -/
theorem stalkFunctor_obj (F : Sheaf S.smallEtaleTopology (Type u)) :
    (stalkFunctor s).obj F = (GeometricPoint.toSmallEtalePoint s).sheafFiber.obj F :=
  sorry

/-- The stalk functor agrees with the presheaf fibre stalk of Definition 59.29.6. -/
theorem stalkFunctor_eq_presheafFiber (F : Sheaf S.smallEtaleTopology (Type u)) :
    (stalkFunctor s).obj F = stalk s F.1 :=
  sorry

/-- The identity geometric point of `Spec k` for the source field of `s̄`. -/
def idGeometricPoint : GeometricPoint (Spec (.of s.K)) :=
  @GeometricPoint.of (Spec (.of s.K)) s.K inferInstance s.isAlgClosed (𝟙 _)

variable [HasWeakSheafify S.smallEtaleTopology (Type u)]
variable [HasWeakSheafify (Spec (.of s.K)).smallEtaleTopology (Type u)]
variable [∀ P : S.Etaleᵒᵖ ⥤ Type u, (smallEtalePullback s.hom).op.HasLeftKanExtension P]
variable [InitiallySmall
    ((smallEtalePullback s.hom ⋙
        (GeometricPoint.toSmallEtalePoint (idGeometricPoint s)).fiber).Elements)]
variable [((smallEtalePullback s.hom).sheafPushforwardContinuous (Type u)
    S.smallEtaleTopology (Spec (.of s.K)).smallEtaleTopology).IsRightAdjoint]

/-- Pullback along `s̄` followed by the sheaf fibre at the identity geometric point of `Spec k`. -/
def pullbackThenSections : Sheaf S.smallEtaleTopology (Type u) ⥤ Type u :=
  (smallEtalePullback s.hom).sheafPullback (Type u)
      S.smallEtaleTopology (Spec (.of s.K)).smallEtaleTopology ⋙
    (GeometricPoint.toSmallEtalePoint (idGeometricPoint s)).sheafFiber

/-- The pullback-then-sections functor evaluates at a sheaf by inverse image then fibre. -/
theorem pullbackThenSections_obj (F : Sheaf S.smallEtaleTopology (Type u)) :
    (pullbackThenSections s).obj F =
      (GeometricPoint.toSmallEtalePoint (idGeometricPoint s)).sheafFiber.obj
        (((smallEtalePullback s.hom).sheafPullback (Type u)
          S.smallEtaleTopology (Spec (.of s.K)).smallEtaleTopology).obj F) :=
  sorry

end AlgebraicGeometry.Scheme.Etale
