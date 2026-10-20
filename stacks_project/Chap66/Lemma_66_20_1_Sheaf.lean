module

public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Subterminal
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap66.Lemma_66_18_3_Site
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.OpenImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.OpenSubspace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Subterminal

/-!
# Representable sheaves of open subspaces on the étale site of algebraic spaces

The reusable representable-sheaf and support API is owned by `ReasLib`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.Etale.ofIsOpenImmersion :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [h : IsOpenImmersion f], Etale f)

#check (AlgebraicGeometry.AlgebraicSpace.spacesEtaleTopology.instSubcanonical :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), (spacesEtaleTopology X).Subcanonical)

#check (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.etale_ι :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (W : OpenSubspace X), Etale W.ι)

#check (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.toSpacesEtale :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (W : OpenSubspace X), spacesEtaleSite X)

#check (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.toSpacesEtale_left :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (W : OpenSubspace X),
    W.toSpacesEtale.left = W.X)

#check (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.toSpacesEtale_hom :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (W : OpenSubspace X),
    W.toSpacesEtale.hom = W.ι)

#check (AlgebraicGeometry.AlgebraicSpace.openSubspaceSheaf :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (W : OpenSubspace X),
    Sheaf (spacesEtaleTopology X) (Type (u + 1)))

#check (AlgebraicGeometry.AlgebraicSpace.openSubspaceSheaf_obj :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (W : OpenSubspace X)
    (U : spacesEtaleSite X),
    (openSubspaceSheaf W).obj.obj (op U) = (U ⟶ W.toSpacesEtale))

#check (AlgebraicGeometry.AlgebraicSpace.nonempty_openSubspaceSheaf_iff :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (W : OpenSubspace X)
    (U : spacesEtaleSite X),
    Nonempty ((openSubspaceSheaf W).obj.obj (op U)) ↔
      ∃ f : U.left ⟶ W.X, f ≫ W.ι = U.hom)

#check (AlgebraicGeometry.AlgebraicSpace.nonempty_openSubspaceSheaf_iff_pointsSet_subset :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (W : OpenSubspace X)
    (U : spacesEtaleSite X),
    Nonempty ((openSubspaceSheaf W).obj.obj (op U)) ↔
      Set.range (Points.map U.hom) ⊆ W.pointsSet)

#check (AlgebraicGeometry.AlgebraicSpace.isSubterminal_openSubspaceSheaf :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (W : OpenSubspace X),
    IsSubterminal (openSubspaceSheaf W))

#check (AlgebraicGeometry.AlgebraicSpace.subterminalOpenSet :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (spacesEtaleTopology X) (Type (u + 1))), Set (Points X))

#check (AlgebraicGeometry.AlgebraicSpace.mem_subterminalOpenSet_iff :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (spacesEtaleTopology X) (Type (u + 1))) (x : Points X),
    x ∈ subterminalOpenSet F ↔
      ∃ U : spacesEtaleSite X, Nonempty (F.obj.obj (op U)) ∧
        x ∈ Set.range (Points.map U.hom))

#check (AlgebraicGeometry.AlgebraicSpace.isOpen_subterminalOpenSet :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (spacesEtaleTopology X) (Type (u + 1))),
    IsOpen (subterminalOpenSet F))

#check (AlgebraicGeometry.AlgebraicSpace.subterminalOpens :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (spacesEtaleTopology X) (Type (u + 1))), Opens (Points X))

#check (AlgebraicGeometry.AlgebraicSpace.subterminalOpens_carrier :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (spacesEtaleTopology X) (Type (u + 1))),
    (subterminalOpens F).carrier = subterminalOpenSet F)

end AlgebraicGeometry.AlgebraicSpace
