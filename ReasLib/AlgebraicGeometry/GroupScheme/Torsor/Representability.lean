module

public import ReasLib.AlgebraicGeometry.GroupScheme.RepresentableTorsor
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Descent.MorphismProperty.Affine
public import ReasLib.CategoryTheory.Sites.GlobalSections.Slice
public import ReasLib.CategoryTheory.Sites.Torsor.Representability

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupScheme

/-- The set-valued carrier of the group sheaf represented by a group scheme is representable. -/
theorem representableGroupCarrier_isRepresentable {S : Scheme.{u}} (τ : StandardTopology)
    (G : Grp (Over S)) :
    ((sheafForget (τ.overTopology S)).obj (representableGroup τ G)).1.IsRepresentable := by
  have hmem : (yonedaGrp (C := Over S)).essImage (yonedaGrp.obj G) :=
    Functor.obj_mem_essImage _ G
  have hrep : ((yonedaGrp.obj G) ⋙ forget GrpCat).IsRepresentable := by
    simpa [essImage_yonedaGrp (C := Over S)] using hmem
  simpa [representableGroup] using hrep

/-- Every fppf sheaf torsor under an affine group scheme has representable carrier. -/
theorem representableOfAffine {S : Scheme.{u}} (G : Grp (Over S))
    [IsAffineHom G.X.hom]
    (P : Sheaf.Torsor (representableGroup .fppf G)) :
    P.carrier.1.IsRepresentable := sorry

end AlgebraicGeometry.GroupScheme
