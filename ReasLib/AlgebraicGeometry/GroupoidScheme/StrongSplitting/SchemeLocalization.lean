module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import ReasLib.AlgebraicGeometry.GroupoidScheme.StrongSplitting.EtaleLocalization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.WithSection.Separated

/-! # Strong splitting after separated étale scheme localization -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- A groupoid scheme satisfying the strong-splitting hypotheses, with flat and
locally finitely presented source and target, admits a separated étale scheme
neighborhood with an isomorphic residue field on which its canonical restriction
is strongly split at the specified point. -/
theorem exists_separatedEtale_scheme_isStronglySplitOver {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.U.left) [StrongSplitting G u]
    [AlgebraicGeometry.Flat G.s.left] [AlgebraicGeometry.Flat G.t.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.s.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.t.left] :
    ∃ (U' : Over S) (g : U' ⟶ G.U) (u' : U'.left),
      IsSeparated g.left ∧ AlgebraicGeometry.Etale g.left ∧ g.left u' = u ∧
        IsIso (g.left.residueFieldMap u') ∧
          GroupoidAlgebraicSpace.IsStronglySplitOver
            (GroupoidAlgebraicSpace.pullback (GroupoidAlgebraicSpace.ofScheme G)
              (objectRestrictionHom G (ofOverMap g)))
            (ofOver.pointsEquiv U' u') :=
  sorry

/-- A groupoid scheme satisfying the strong-splitting hypotheses, with flat and
locally finitely presented source and target, admits a separated étale scheme
neighborhood and a morphism from the residue field at which the canonical
restriction is strongly split. The commuting equation with the original residue
morphism, together with étaleness, ensures preservation of the residue field;
the domain of the residue morphism alone does not ensure this. -/
theorem exists_separatedEtale_residueMap_isStronglySplitOver {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.U.left) [StrongSplitting G u]
    [AlgebraicGeometry.Flat G.s.left] [AlgebraicGeometry.Flat G.t.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.s.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.t.left] :
    ∃ (U' : Over S) (g : U' ⟶ G.U)
      (u' : ofOver (residueOver G u) ⟶ ofOver U'),
      IsSeparated g.left ∧ AlgebraicGeometry.Etale g.left ∧
        u' ≫ ofOverMap g = residueMap G u ∧
          GroupoidAlgebraicSpace.IsStronglySplitOver
            (GroupoidAlgebraicSpace.pullback (GroupoidAlgebraicSpace.ofScheme G)
              (objectRestrictionHom G (ofOverMap g)))
            (residueFieldPoint G u u') :=
  sorry

end AlgebraicGeometry.GroupoidScheme
