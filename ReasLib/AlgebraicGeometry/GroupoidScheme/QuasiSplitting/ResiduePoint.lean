module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.ResiduePoint
public import ReasLib.AlgebraicGeometry.GroupoidScheme.QuasiSplitting

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicSpace Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The points of the residue source fibre mapping to the identity arrow form an open set. -/
private theorem identityOpen_isOpen {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [IsQuasiSplittingSituation G u] :
    IsOpen
      {z |
        Points.map
            (pullback.snd (residueMap G u) (GroupoidAlgebraicSpace.ofScheme G).s.left) z =
          Points.map (GroupoidAlgebraicSpace.ofScheme G).e.left (ofOver.pointsEquiv G.U u)} :=
  sorry

/-- The support `Z_u ⊂ |Spec(κ(u)) ×_U R|` of points mapping to the identity
arrow `e(u)`. -/
def identityOpen {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left)
    [IsQuasiSplittingSituation G u] :
    Opens
      (Points
        (pullback (residueMap G u) (GroupoidAlgebraicSpace.ofScheme G).s.left)) where
  carrier :=
    {z |
      Points.map
          (pullback.snd (residueMap G u) (GroupoidAlgebraicSpace.ofScheme G).s.left) z =
        Points.map (GroupoidAlgebraicSpace.ofScheme G).e.left (ofOver.pointsEquiv G.U u)}
  is_open' := by exact identityOpen_isOpen G u

/-- Membership in `identityOpen G u` is equivalent to landing at the identity
arrow `e(u)`. -/
theorem mem_identityOpen {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left)
    [IsQuasiSplittingSituation G u]
    (z :
      Points
        (pullback (residueMap G u) (GroupoidAlgebraicSpace.ofScheme G).s.left)) :
    z ∈ identityOpen G u ↔
      Points.map
          (pullback.snd (residueMap G u) (GroupoidAlgebraicSpace.ofScheme G).s.left) z =
        Points.map (GroupoidAlgebraicSpace.ofScheme G).e.left (ofOver.pointsEquiv G.U u) :=
  Iff.rfl

/-- The identity-support open of the residue source fibre is finite over the residue field. -/
private theorem identityWithSection_isFinite {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [IsQuasiSplittingSituation G u] :
    AlgebraicSpace.IsFinite ((OpenSubspace.fromOpens (identityOpen G u)).ι ≫
      pullback.fst (residueMap G u) (GroupoidAlgebraicSpace.ofScheme G).s.left) :=
  sorry

/-- The unit section over the residue point lands in the identity-support open. -/
private theorem identityWithSection_contains_unit {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [IsQuasiSplittingSituation G u] :
    Set.range (Points.map (FinitePart.unitSection (residueMap G u)
      (GroupoidAlgebraicSpace.ofScheme G).s.left
      (GroupoidAlgebraicSpace.ofScheme G).e.left
      (GroupoidAlgebraicSpace.unit_source_left (GroupoidAlgebraicSpace.ofScheme G)))) ⊆
      identityOpen G u :=
  sorry

/-- The pair `(u, Z_u)` as a `Spec(κ(u))`-point of `(R_s / U, e)_fin`. -/
def identityWithSection {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left)
    [IsQuasiSplittingSituation G u] :
    FinitePart.WithSection.Point (GroupoidAlgebraicSpace.ofScheme G).s.left
      (GroupoidAlgebraicSpace.ofScheme G).e.left
      (GroupoidAlgebraicSpace.unit_source_left (GroupoidAlgebraicSpace.ofScheme G))
      (residueOver G u) where
  a := residueMap G u
  Z := identityOpen G u
  isFinite := by exact identityWithSection_isFinite G u
  contains_unit := by exact identityWithSection_contains_unit G u

/-- The object map of `identityWithSection G u` is `residueMap G u`. -/
theorem identityWithSection_a {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [IsQuasiSplittingSituation G u] :
    (identityWithSection G u).a = residueMap G u :=
  rfl

/-- The morphism `u' : Spec(κ(u)) ⟶ U'` classifying the pair `(u, Z_u)`. -/
def quasiSplittingHom {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left)
    [IsQuasiSplittingSituation G u] :
    ofOver (residueOver G u) ⟶
      (GroupoidAlgebraicSpace.finitePart (GroupoidAlgebraicSpace.ofScheme G)).U.left :=
  GroupoidAlgebraicSpace.withSectionHom (GroupoidAlgebraicSpace.ofScheme G)
    (identityWithSection G u)

/-- The classifying morphism `u'` lies over `u : Spec(κ(u)) ⟶ U`. -/
theorem quasiSplittingHom_liesOver {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [IsQuasiSplittingSituation G u] :
    quasiSplittingHom G u ≫
        GroupoidAlgebraicSpace.finitePartToU (GroupoidAlgebraicSpace.ofScheme G) =
      residueMap G u :=
  GroupoidAlgebraicSpace.withSectionHom_toU (GroupoidAlgebraicSpace.ofScheme G)
    (identityWithSection G u)

/-- The point of `|U'|` determined by the residue-field morphism `u'`. -/
def quasiSplittingResiduePoint {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [IsQuasiSplittingSituation G u] :
    Points (GroupoidAlgebraicSpace.finitePart (GroupoidAlgebraicSpace.ofScheme G)).U.left :=
  residueFieldPoint G u (quasiSplittingHom G u)

/-- `quasiSplittingResiduePoint` is the residue-field point of
`quasiSplittingHom`. -/
theorem quasiSplittingResiduePoint_eq {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [IsQuasiSplittingSituation G u] :
    quasiSplittingResiduePoint G u =
      residueFieldPoint G u (quasiSplittingHom G u) :=
  rfl

end AlgebraicGeometry.GroupoidScheme
