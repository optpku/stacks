module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.StructureSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening

/-!
# Ringed-topos comparison for thickenings of algebraic spaces

The spaces-étale site of an algebraic space carries the inverse image of the
structure sheaf along any morphism. The canonical comparison to the target's
ringed topos has identity structure map and is an equivalence for a thickening.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Thickening

variable {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X')

/-- The spaces-étale ringed site of `X` equipped with the inverse-image sheaf
`𝒪_{X'}`, i.e. `(X_spaces,étale, 𝒪_{X'})`. -/
abbrev closedRingedSite : RingedSite.{u + 1, u + 1, u} :=
  RingedSite.ofRingSheaf (spacesEtaleTopology X) (closedStructureSheaf i)

/-- The structure sheaf of `closedRingedSite i` is `closedStructureSheaf i`. -/
theorem closedRingedSite_structureSheaf :
    (closedRingedSite i).structureSheaf = closedStructureSheaf i :=
  rfl

/-- The site topology of `closedRingedSite i` is `spacesEtaleTopology X`. -/
theorem closedRingedSite_siteTopology :
    (closedRingedSite i).siteTopology = spacesEtaleTopology X :=
  rfl

/-- The canonical comparison of ringed topoi
`(Sh(X_spaces,étale), 𝒪_{X'}) ⟶ (Sh(X'_spaces,étale), 𝒪_{X'})`, with underlying
morphism of topoi that of `spacesRingedToposHom i` and identity inverse-image
structure map. -/
def closedRingedToposHom :
    RingedSite.ToposHom (closedRingedSite i) (spacesRingedSite X') where
  toTopos := (spacesRingedToposHom i).toTopos
  structureMap := 𝟙 _

/-- The underlying morphism of topoi of `closedRingedToposHom i` is that of
`spacesRingedToposHom i`. -/
theorem closedRingedToposHom_toTopos :
    (closedRingedToposHom i).toTopos = (spacesRingedToposHom i).toTopos :=
  rfl

/-- The inverse-image structure map of `closedRingedToposHom i` is the identity. -/
theorem closedRingedToposHom_structureMap :
    (closedRingedToposHom i).structureMap = 𝟙 _ :=
  rfl

/-- If `i` is a thickening, then `closedRingedToposHom i` is an equivalence of
ringed topoi, identifying `(Sh(X'_spaces,étale), 𝒪_{X'})` with
`(Sh(X_spaces,étale), 𝒪_{X'})`. -/
instance closedRingedToposHom_isEquivalence_of_isThickening [IsThickening i] :
    (closedRingedToposHom i).IsEquivalence := sorry

end AlgebraicGeometry.AlgebraicSpace.Thickening
