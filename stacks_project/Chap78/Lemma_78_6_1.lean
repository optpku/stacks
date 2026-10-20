module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group.Separation
import StacksCheckRecall

/-!
# Separation properties of group algebraic spaces

The structure morphism of a group algebraic space is separated (resp.
quasi-separated, resp. locally separated) if and only if the identity
section is a closed immersion (resp. quasi-compact, resp. an immersion).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped CategoryTheory.MonObj

noncomputable section

universe u

/- Lemma 78.6.1 (1): let `S` be a scheme, let `B` be an algebraic space over `S`,
and let `G` be a group algebraic space over `B`. Then `G.X.hom` is separated if
and only if the identity section `η[G.X].left` is a closed immersion. -/
@[stacks 06P6] #check
  (AlgebraicGeometry.GroupAlgebraicSpace.isSeparated_iff_isClosedImmersion_one :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B),
      AlgebraicSpace.Separated G.X.hom ↔ AlgebraicSpace.IsClosedImmersion η[G.X].left)

/- Lemma 78.6.1 (2): let `S` be a scheme, let `B` be an algebraic space over `S`,
and let `G` be a group algebraic space over `B`. Then `G.X.hom` is quasi-separated
if and only if the identity section `η[G.X].left` is quasi-compact. -/
@[stacks 06P6] #check
  (AlgebraicGeometry.GroupAlgebraicSpace.quasiSeparated_iff_quasiCompact_one :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B),
      AlgebraicSpace.QuasiSeparated G.X.hom ↔ AlgebraicSpace.QuasiCompact η[G.X].left)

/- Lemma 78.6.1 (3): let `S` be a scheme, let `B` be an algebraic space over `S`,
and let `G` be a group algebraic space over `B`. Then `G.X.hom` is locally
separated if and only if the identity section `η[G.X].left` is an immersion. -/
@[stacks 06P6] #check
  (AlgebraicGeometry.GroupAlgebraicSpace.locallySeparated_iff_isImmersion_one :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B),
      AlgebraicSpace.LocallySeparated G.X.hom ↔ AlgebraicSpace.IsImmersion η[G.X].left)
