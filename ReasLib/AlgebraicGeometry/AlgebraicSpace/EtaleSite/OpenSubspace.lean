module

public import Mathlib.CategoryTheory.Subterminal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.OpenImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Subcanonical
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support

/-! # Representable sheaves of open subspaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace OpenSubspace

/-- The inclusion of an open subspace is étale. -/
theorem etale_ι {S : Scheme.{u}} {X : AlgebraicSpace S} (W : OpenSubspace X) :
    Etale W.ι :=
  Etale.ofIsOpenImmersion (f := W.ι) (h := W.isOpenImmersion)

/-- The object of `X_spaces,étale` determined by an open subspace. -/
def toSpacesEtale {S : Scheme.{u}} {X : AlgebraicSpace S} (W : OpenSubspace X) :
    spacesEtaleSite X :=
  MorphismProperty.Over.mk ⊤ W.ι (OpenSubspace.etale_ι W)

/-- The underlying algebraic space of `toSpacesEtale W` is `W`. -/
@[simp]
theorem toSpacesEtale_left {S : Scheme.{u}} {X : AlgebraicSpace S} (W : OpenSubspace X) :
    W.toSpacesEtale.left = W.X :=
  rfl

/-- The structural morphism of `toSpacesEtale W` is the inclusion of `W`. -/
@[simp]
theorem toSpacesEtale_hom {S : Scheme.{u}} {X : AlgebraicSpace S} (W : OpenSubspace X) :
    W.toSpacesEtale.hom = W.ι :=
  rfl

end OpenSubspace

/-- The representable sheaf `h_W` on `X_spaces,étale` associated to an open subspace `W ⊂ X`. -/
def openSubspaceSheaf {S : Scheme.{u}} {X : AlgebraicSpace S} (W : OpenSubspace X) :
    Sheaf (spacesEtaleTopology X) (Type (u + 1)) :=
  (spacesEtaleTopology X).yoneda.obj W.toSpacesEtale

/-- Sections of `openSubspaceSheaf W` over `U` are morphisms `U ⟶ W` over `X`. -/
theorem openSubspaceSheaf_obj {S : Scheme.{u}} {X : AlgebraicSpace S} (W : OpenSubspace X)
    (U : spacesEtaleSite X) :
    (openSubspaceSheaf W).obj.obj (op U) = (U ⟶ W.toSpacesEtale) :=
  rfl

/-- `openSubspaceSheaf W` has a section over `U` if and only if `U → X` factors through `W`. -/
theorem nonempty_openSubspaceSheaf_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (W : OpenSubspace X) (U : spacesEtaleSite X) :
    Nonempty ((openSubspaceSheaf W).obj.obj (op U)) ↔
      ∃ f : U.left ⟶ W.X, f ≫ W.ι = U.hom :=
  sorry

/-- `openSubspaceSheaf W` has a section over `U` exactly when the image of `|U|` lies in `|W|`. -/
theorem nonempty_openSubspaceSheaf_iff_pointsSet_subset {S : Scheme.{u}} {X : AlgebraicSpace S}
    (W : OpenSubspace X) (U : spacesEtaleSite X) :
    Nonempty ((openSubspaceSheaf W).obj.obj (op U)) ↔
      Set.range (Points.map U.hom) ⊆ W.pointsSet :=
  sorry

/-- The representable sheaf of an open subspace is subterminal. -/
theorem isSubterminal_openSubspaceSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (W : OpenSubspace X) : IsSubterminal (openSubspaceSheaf W) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
