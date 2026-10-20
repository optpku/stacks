module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.Openness
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.OpenSubspace

/-! # Subterminal sheaves on the spaces-étale site -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The points lying in the image of an étale object with a nonempty section of `F`. -/
def subterminalOpenSet {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (spacesEtaleTopology X) (Type (u + 1))) : Set (Points X) :=
  {x | ∃ U : spacesEtaleSite X, Nonempty (F.obj.obj (op U)) ∧
    x ∈ Set.range (Points.map U.hom)}

/-- Membership in `subterminalOpenSet F` is existence of an étale neighbourhood with a
nonempty section whose image contains the point. -/
theorem mem_subterminalOpenSet_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (spacesEtaleTopology X) (Type (u + 1))) (x : Points X) :
    x ∈ subterminalOpenSet F ↔
      ∃ U : spacesEtaleSite X, Nonempty (F.obj.obj (op U)) ∧
        x ∈ Set.range (Points.map U.hom) :=
  by
    change (∃ U : spacesEtaleSite X, Nonempty (F.obj.obj (op U)) ∧
      x ∈ Set.range (Points.map U.hom)) ↔ _
    rfl

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
  rfl

/-- A subterminal sheaf on the spaces-étale site is represented by a unique open subspace. -/
theorem existsUnique_open_iso_openSubspaceSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (spacesEtaleTopology X) (Type (u + 1))) (hF : IsSubterminal F) :
    ∃ U : OpenSubspace X,
      Nonempty (F ≅ openSubspaceSheaf U) ∧
        ∀ V : OpenSubspace X, Nonempty (F ≅ openSubspaceSheaf V) →
          V.pointsOpens = U.pointsOpens :=
  sorry

/-- A subterminal sheaf is represented by `U` exactly when `U` is its support open. -/
theorem nonempty_iso_openSubspaceSheaf_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (spacesEtaleTopology X) (Type (u + 1))) (hF : IsSubterminal F)
    (U : OpenSubspace X) :
    Nonempty (F ≅ openSubspaceSheaf U) ↔ U.pointsOpens = subterminalOpens F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
