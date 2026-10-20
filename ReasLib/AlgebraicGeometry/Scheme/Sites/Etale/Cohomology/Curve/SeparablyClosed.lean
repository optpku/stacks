module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Pullback
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Topology.KrullDimension

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Sheaf

universe u

namespace AlgebraicGeometry.Scheme.Etale.CurveCohomology

variable [∀ Y : Scheme.{u}, HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ Y : Scheme.{u}, HasExt.{u} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {S T : Scheme.{u}} (f : T ⟶ S),
  ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
    S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]

/-- For a proper scheme of dimension at most one over a separably closed field,
canonical étale cohomology pullback with locally torsion abelian coefficients is an
isomorphism in every degree under an extension of separably closed ground fields. -/
theorem cohomologyPullback_isIso_of_isProper_of_isSepClosed
    {k : Type u} [Field k] [IsSepClosed k]
    (X : SchemeOverField k) (h_dim : topologicalKrullDim X.left ≤ 1)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsLocallyTorsion F) (h_proper : IsProper X.hom)
    {k' : Type u} [Field k'] [IsSepClosed k'] [Algebra k k']
    (X' : SchemeOverField k') (π : X'.left ⟶ X.left)
    (h_baseChange : IsPullback π X'.hom X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    (q : ℕ) : IsIso (cohomologyPullback π F q) := sorry

end AlgebraicGeometry.Scheme.Etale.CurveCohomology
