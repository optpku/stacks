module

public import stacks_project.Chap63.Definition_63_3_7_CompactSupport

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Lemma 63.3.8: if `X` is a proper scheme over a field `k`, then for an abelian
sheaf `F` on `X_étale` the compactly supported global sections equal all global
sections: `H^0_c(X, F) = H^0(X, F)`. -/
@[stacks 0F73]
theorem globalSectionsCompactSupport_eq_univ
    {k : Type u} [Field k] {X : SchemeOverField k} [IsProper X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    globalSectionsCompactSupport F = Set.univ :=
  sorry

/-- Every global étale section has compact support when `X` is proper over a field. -/
theorem hasCompactSupport_of_isProper
    {k : Type u} [Field k] {X : SchemeOverField k} [IsProper X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : F.obj.obj (op (globalEtale X.left))) :
    HasCompactSupport F σ :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
