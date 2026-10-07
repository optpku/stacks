module

public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Subterminal
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap66.Lemma_66_18_3_Site
public import stacks_project.Chap66.Lemma_66_4_8_Opens

/-!
# Representable sheaves of open subspaces on the étale site of algebraic spaces

An open subspace `W ⊂ X` determines an object of `X_spaces,étale` and hence a
representable sheaf `h_W` on `spacesEtaleTopology X`. A subterminal sheaf has
support the union of images of objects with a nonempty section.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Etale

/-- An open immersion of algebraic spaces is étale. -/
instance ofIsOpenImmersion {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [IsOpenImmersion f] : Etale f :=
  sorry

end Etale

/-- The étale topology of algebraic spaces over `X` is subcanonical. -/
instance spacesEtaleTopology.instSubcanonical {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (spacesEtaleTopology X).Subcanonical :=
  sorry

namespace OpenSubspace

/-- The inclusion of an open subspace is étale. -/
instance etale_ι {S : Scheme.{u}} {X : AlgebraicSpace S} (W : OpenSubspace X) :
    Etale W.ι :=
  sorry

/-- The object of `X_spaces,étale` determined by an open subspace. -/
def toSpacesEtale {S : Scheme.{u}} {X : AlgebraicSpace S} (W : OpenSubspace X) :
    spacesEtaleSite X :=
  MorphismProperty.Over.mk ⊤ W.ι inferInstance

/-- The underlying algebraic space of `toSpacesEtale W` is `W`. -/
@[simp]
theorem toSpacesEtale_left {S : Scheme.{u}} {X : AlgebraicSpace S} (W : OpenSubspace X) :
    W.toSpacesEtale.left = W.X :=
  sorry

/-- The structural morphism of `toSpacesEtale W` is the inclusion of `W`. -/
@[simp]
theorem toSpacesEtale_hom {S : Scheme.{u}} {X : AlgebraicSpace S} (W : OpenSubspace X) :
    W.toSpacesEtale.hom = W.ι :=
  sorry

end OpenSubspace

/-- The representable sheaf `h_W` on `X_spaces,étale` associated to an open subspace `W ⊂ X`. -/
def openSubspaceSheaf {S : Scheme.{u}} {X : AlgebraicSpace S} (W : OpenSubspace X) :
    Sheaf (spacesEtaleTopology X) (Type (u + 1)) :=
  (spacesEtaleTopology X).yoneda.obj W.toSpacesEtale

/-- Sections of `openSubspaceSheaf W` over `U` are morphisms `U ⟶ W` over `X`. -/
theorem openSubspaceSheaf_obj {S : Scheme.{u}} {X : AlgebraicSpace S} (W : OpenSubspace X)
    (U : spacesEtaleSite X) :
    (openSubspaceSheaf W).obj.obj (op U) = (U ⟶ W.toSpacesEtale) :=
  sorry

/-- `openSubspaceSheaf W` has a section over `U` if and only if `U → X` factors through `W`. -/
theorem nonempty_openSubspaceSheaf_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (W : OpenSubspace X) (U : spacesEtaleSite X) :
    Nonempty ((openSubspaceSheaf W).obj.obj (op U)) ↔
      ∃ f : U.left ⟶ W.X, f ≫ W.ι = U.hom :=
  sorry

/-- `openSubspaceSheaf W` has a section over `U` if and only if the image of `|U|` lies in `|W|`. -/
theorem nonempty_openSubspaceSheaf_iff_pointsSet_subset {S : Scheme.{u}} {X : AlgebraicSpace S}
    (W : OpenSubspace X) (U : spacesEtaleSite X) :
    Nonempty ((openSubspaceSheaf W).obj.obj (op U)) ↔
      Set.range (Points.map U.hom) ⊆ W.pointsSet :=
  sorry

/-- The representable sheaf of an open subspace is subterminal. -/
theorem isSubterminal_openSubspaceSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (W : OpenSubspace X) : IsSubterminal (openSubspaceSheaf W) :=
  sorry

/-- A sheaf of types on `X_spaces,étale` is subterminal if and only if it has at most one
section over every object. -/
theorem isSubterminal_sheaf_iff_subsingleton_obj {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (spacesEtaleTopology X) (Type (u + 1))) :
    IsSubterminal F ↔ ∀ U : spacesEtaleSite X, Subsingleton (F.obj.obj (op U)) :=
  sorry

/-- The set of points of `|X|` that lie in the image of some étale `U → X` with a nonempty
section of `F`. -/
def subterminalOpenSet {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (spacesEtaleTopology X) (Type (u + 1))) : Set (Points X) :=
  {x | ∃ U : spacesEtaleSite X, Nonempty (F.obj.obj (op U)) ∧ x ∈ Set.range (Points.map U.hom)}

/-- Membership in `subterminalOpenSet F` is existence of an étale neighbourhood with a
nonempty section whose image contains the point. -/
theorem mem_subterminalOpenSet_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (spacesEtaleTopology X) (Type (u + 1))) (x : Points X) :
    x ∈ subterminalOpenSet F ↔
      ∃ U : spacesEtaleSite X, Nonempty (F.obj.obj (op U)) ∧
        x ∈ Set.range (Points.map U.hom) :=
  sorry

/-- The support of a type-valued étale sheaf in the sense of `subterminalOpenSet` is open. -/
theorem isOpen_subterminalOpenSet {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (spacesEtaleTopology X) (Type (u + 1))) :
    IsOpen (subterminalOpenSet F) :=
  sorry

/-- The open of `|X|` underlying `subterminalOpenSet F`. -/
def subterminalOpens {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (spacesEtaleTopology X) (Type (u + 1))) : Opens (Points X) :=
  Opens.mk (subterminalOpenSet F) (isOpen_subterminalOpenSet F)

/-- The carrier of `subterminalOpens F` is `subterminalOpenSet F`. -/
theorem subterminalOpens_carrier {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (spacesEtaleTopology X) (Type (u + 1))) :
    (subterminalOpens F).carrier = subterminalOpenSet F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
