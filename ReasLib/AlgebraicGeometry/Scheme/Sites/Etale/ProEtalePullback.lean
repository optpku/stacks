/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtaleSections
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig.Sections

/-!
# Inverse image from the small étale site to the small pro-étale site

The presheaf of global sections of small étale inverse images is a sheaf on
the small pro-étale site and is isomorphic to comparison inverse image.
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}
variable [∀ Y : Scheme.{u}, HasSheafify Y.smallEtaleTopology (Type (u + 1))]
variable [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z),
  ∀ P : Z.Etaleᵒᵖ ⥤ Type (u + 1),
    (smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ Type (u + 1),
  (etaleToProEt X).op.HasLeftKanExtension P]
variable [HasWeakSheafify (ProEt.topology X) (Type (u + 1))]

/-- Global sections of small étale inverse images form a sheaf on the small
pro-étale site. -/
theorem etalePullbackGamma_isSheaf
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    Presheaf.IsSheaf (ProEt.topology X) (etalePullbackGamma F) := sorry

/-- The sheaf on the small pro-étale site whose sections over a weakly étale
`f : Y ⟶ X` are the global sections of the small étale inverse image of `F`. -/
def etalePullbackGammaSheaf
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    Sheaf (ProEt.topology X) (Type (u + 1)) :=
  ⟨etalePullbackGamma F, etalePullbackGamma_isSheaf F⟩

/-- The sheaf of global sections of small étale inverse images is isomorphic
to inverse image along the étale-to-pro-étale comparison. -/
theorem etalePullbackGammaSheaf_iso
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    IsIsomorphic (etalePullbackGammaSheaf F)
      ((etaleToProEtPullback X (Type (u + 1))).obj F) := sorry

end AlgebraicGeometry.Scheme
