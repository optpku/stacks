/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtaleComparison

/-!
# Fully faithful inverse image from the étale to the pro-étale site

The adjunction unit of the étale-to-pro-étale comparison is an isomorphism,
and its evaluation gives an isomorphism on sections over étale objects.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.EtaleToProEt

variable (X : Scheme.{u})
variable [∀ P : X.Etaleᵒᵖ ⥤ Type (u + 1), (etaleToProEt X).op.HasLeftKanExtension P]
variable [HasWeakSheafify (ProEt.topology X) (Type (u + 1))]

/-- For every sheaf of sets on the small étale site, the component of the
adjunction unit `F ⟶ ε_* ε⁻¹ F` is an isomorphism. -/
instance unit_app_isIso (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    IsIso ((etaleToProEt_sheafAdjunction X (Type (u + 1))).unit.app F) := sorry

/-- The adjunction unit of the étale-to-pro-étale inverse image and direct
image functors on sheaves of sets is an isomorphism. -/
instance unit_isIso :
    IsIso (etaleToProEt_sheafAdjunction X (Type (u + 1))).unit := sorry

/-- The comparison on sections over an étale object is the adjunction unit
followed by the canonical identification of direct image with restriction. -/
def obj_etale (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : X.Etale) :
    F.obj.obj (op U) ⟶
      (((etaleToProEtPullback X (Type (u + 1))).obj F).obj.obj
        (op ((etaleToProEt X).obj U))) :=
  ((etaleToProEt_sheafAdjunction X (Type (u + 1))).unit.app F).hom.app (op U) ≫
    (etaleToProEtSheaf_obj_obj X ((etaleToProEtPullback X (Type (u + 1))).obj F) U).hom

/-- The comparison on sections from an étale sheaf to its pro-étale inverse
image is an isomorphism at every étale object. -/
instance obj_etale_isIso (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : X.Etale) :
    IsIso (obj_etale X F U) := sorry

end AlgebraicGeometry.Scheme.EtaleToProEt
